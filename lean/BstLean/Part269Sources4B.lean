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
import BstLean.Part269Direction4
import BstLean.Part269Shared4
import BstLean.Part269Finite
import BstLean.Part269Rows4
import BstLean.Part269Source
/-! Actual 12463 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12463
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12463 ≤ (1.036151105582 : ℝ) := by
  have hr : (111.637807216014 : ℝ) ≤ √(12463 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.637807216014 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12463 12463 (11 / 1000) ≤
    (0.008562395866 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12463) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.637807216014 : ℝ) ≤ √(12463 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12463)
  have hdiv : K / √(12463 : ℝ) ≤ K / 111.637807216014 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.637807216014 ≤ (0.008562395866 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12463.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12463 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12463 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12463 := gPlus_lower 12463
end BstLean.Part269.N12463

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12463
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036151105581 : ℝ) ≤ wn 12463 := by
  have hn : √(12463 : ℝ) ≤ 111.637807216015 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12463 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.637807216015 ≤ 2 / √(12463 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256755426 : ℝ) ≤ rhoBar 12463 BstLean.Part154.csC ∧
    rhoBar 12463 BstLean.Part154.csC ≤ 0.000256755824 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036151105581 : ℝ) / (1.295212 * 12463) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036151105582 : ℝ) / (1.29521 * 12463) := by gcongr
      _ ≤ (0.000256755824 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12463 BstLean.Part154.csC) ≤ 0.001027089220 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12463 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12463 BstLean.Part154.csC) (piBar (rhoBar 12463 BstLean.Part154.csC)) ≤ 0.000196112007 ∧
    cc1 (rhoBar 12463 BstLean.Part154.csC) (piBar (rhoBar 12463 BstLean.Part154.csC)) ≤ 0.000124787336 ∧
    cc2 (rhoBar 12463 BstLean.Part154.csC) ≤ 0.000072439960 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12463 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12463 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12463 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12463 BstLean.Part154.csC * nuR (rhoBar 12463 BstLean.Part154.csC)) ≤ 0.000513528129 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256755824 : ℝ) * 0.001027089220 := by gcongr
      _ ≤ (0.000513528129 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12463 BstLean.Part154.csC) * nuR (rhoBar 12463 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001027089220 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12463 BstLean.Part154.csC) * rhoBar 12463 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256755824 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256755824 / 2 + 0.399 * 0.001027089220 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196112007 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513528129 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124787336 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256755824 / 1.414213562 := by gcongr
      _ ≤ (0.000072439960 : ℝ) := by norm_num

end BstLean.Part269.N12463

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12463
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12463 BstLean.Part154.csC) (piBar (rhoBar 12463 BstLean.Part154.csC)) ≤ 1.66090E-7 := by
  have hr0 : 0 ≤ rhoBar 12463 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12463 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12463 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12463 BstLean.Part154.csC) (piBar (rhoBar 12463 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12463 BstLean.Part154.csC) (piBar (rhoBar 12463 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12463 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196112007 : ℝ) ^ 2 + 0.000124787336 ^ 2 + 3 * 0.000072439960 ^ 2 +
        2 * 0.797885 * 0.000196112007 * 0.000124787336 + 2 * 0.000196112007 * 0.000072439960 +
        4 * 0.797885 * 0.000124787336 * 0.000072439960 := by gcongr
    _ ≤ (1.66090E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12463 BstLean.Part154.csC Θ ≤ 0.002681062517 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12463 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12463 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12463 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12463 BstLean.Part154.csC) (piBar (rhoBar 12463 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12463 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036151105582 * 1.66090E-7 / (0.000256755426 : ℝ) := by gcongr
    _ ≤ 0.002681062517 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12463 BstLean.Part154.csC Θ ≤ 0.002975763224 + 0.000677459915 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12463 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12463 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12463 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036151105582 : ℝ) * ((2 * Θ * 0.000256755824 +
        (6863 / 10000) * 0.000256755824 * 12463 * 0.001027089220) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002975763224 + 0.000677459915 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12463 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12463 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12463 0.011 Θ ∧ gammaRatio 12463 0.011 Θ ≤ 0.000088266013 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12463 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036151105582 : ℝ) * 0.525 / ((1 - 0.011) * 12463) := by gcongr
      _ ≤ (0.000088266013 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12463 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12463 0.011 Θ) :=
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
    badAllowance 12463 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12463 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12463 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12463 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12463 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12463 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12463 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12463 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12463 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12463 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12463 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036151105582 : ℝ) * 12463 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12463 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003792137970 + 0.003358522432 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12463

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12463
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12463 BstLean.Part154.csC) (piBar (rhoBar 12463 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12463 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12463 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12463 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12463 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12463 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12463 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12463 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12463 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12463 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12463 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12463 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12463 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12463 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12463 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052986427765 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12463) ≤ 0.010697429580 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12463 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036151105582)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010697429580 + 2 * 0.737676 / 12463) := by gcongr
    _ ≤ (0.052986427765 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12463 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12463

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12463
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492646634 : ℝ) ≤ plow 12463 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12463) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053061962247)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407557822) : eMP 12463 0.011 xi bn ≤ 0.001211446546 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12463 : ℝ) * (1 - 0.011))) ≤ 0.000598961130 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001407557822 / (12463 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598961130 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598961130 : ℝ) + 3.141593 * 0.053061962247 / (12463 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001211446546 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053061962247)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407557822) : PiBarMP 12463 12 0.011 xi bn ≤ 0.162792799593 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12463 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037517433575 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.022101403279 : ℝ) ≤ √((12463 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.637807216014 : ℝ) ≤ √(12463 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12463) ≤ 0.124800088879 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037517433575 + 0.053061962247 * 1.772454 / (2 * (111.022101403279 : ℝ))) * (1 + 0.001211446546) +
        8 / (12463 * 111.637807216014) + 0.124800088879 := by gcongr
    _ ≤ (0.162792799593 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053061962247)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407557822) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283338250521) :
    parallelOracle 12463 0.011 xi bn cd ≤ 0.163802881162 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12463 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12463 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492646634 : ℝ) ≤ plow 12463 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.637807216014 : ℝ) ≤ √(12463 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283338250521 : ℝ) / (2 * 0.560492646634 * 111.637807216014)) * 0.162792799593 +
        0.283338250521 ^ 2 / (2 * 0.560492646634 * 111.637807216014) := by gcongr
    _ ≤ (0.163802881162 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053061962247) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407557822)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283338250521) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12463 12463 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492646634 : ℝ) ≤ plow 12463 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.637807216014 : ℝ) ≤ √(12463 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12463 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12463 Θ 1.22 ≤ 0.011878596804 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.637807216014 := by gcongr <;> linarith
      _ ≤ (0.011878596804 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12463 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12463 12463 0.011 ≤ 0.008562395866 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12463 12463 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12463 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12463 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12463 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12463 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163802881162 + 0.011878596804 + (0.008562395866 : ℝ) *
        (1 + 2 * (0.283338250521 + 0.011878596804) / (0.560492646634 * 111.637807216014))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12463]

end BstLean.Part269.N12463

/-! The original eight local profiles supply actual 12463 moment certificates. -/
namespace BstLean.Part269.N12463
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12463 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12463 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12463 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053061962247 ∧
    0 ≤ bN 12463 BstLean.Part154.csC (groupTheta g) ∧ bN 12463 BstLean.Part154.csC (groupTheta g) ≤ 0.001407557822 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12463 12463 0.011
      (momentAllowance 12463 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12463 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12463 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12463 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12463 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12463 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230351822756 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12463 0.011
      (momentAllowance 12463 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12463 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12463
/-! The actual computed-centre upper energy formula at 12463. -/
namespace BstLean.Part269.N12463
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12463

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12463
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12463)
open BstLean.Part268 (cell12463)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086214494627
  | 2 => 0.087171330523
  | 3 => 0.088128484221
  | 4 => 0.089087866011
  | 5 => 0.090051768578
  | 6 => 0.091022921417
  | 7 => 0.092004549944
  | 8 => 0.093000439256
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12463 12463 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12463 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003795409572 + 0.003362150420 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S4.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12463

/-! Actual upper energy certificates on all 43 source endpoints at 12463. -/
namespace BstLean.Part269.N12463
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12463)
open BstLean.Part268 (cell12463)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12463 (gMinus 12463) (1 - (cell12463 i).lower) ≤ 1 ∧
    energyUpper 12463 (gMinus 12463) (BstLean.Part211.gPlus 12463)
      (finiteEnergy 12463 12463 0.011) (1 - (cell12463 i).lower) ≤
      (cell12463 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨10,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨11,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨12,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨13,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨14,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨15,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨16,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨17,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨18,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨19,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨20,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨21,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨22,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨23,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨24,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨25,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨26,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨27,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨28,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨29,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨30,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨31,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨32,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨33,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨34,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨35,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨36,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨37,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨38,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨39,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨40,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨41,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨42,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨43,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨44,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨45,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨46,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨47,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨48,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨49,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨50,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨51,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12463) (by norm_num)
        (q := 1 - (cell12463 ⟨52,by decide⟩).lower)
        (by norm_num [cell12463]) (by norm_num [cell12463])
      exact ⟨E.1,E.2.trans (by norm_num [cell12463])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12463

/-! Source-cell containment and simple scalar guards at 12463. -/
namespace BstLean.Part269.N12463
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12463)
open BstLean.Part268 (cell12463)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12463 ⟨10,by decide⟩).lower ∧ (cell12463 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12463 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12463 ⟨11,by decide⟩).lower ∧ (cell12463 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12463 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12463 ⟨12,by decide⟩).lower ∧ (cell12463 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12463 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12463 ⟨13,by decide⟩).lower ∧ (cell12463 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12463 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12463 ⟨14,by decide⟩).lower ∧ (cell12463 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12463 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12463 ⟨15,by decide⟩).lower ∧ (cell12463 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12463 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12463 ⟨16,by decide⟩).lower ∧ (cell12463 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12463 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12463 ⟨17,by decide⟩).lower ∧ (cell12463 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12463 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12463 ⟨18,by decide⟩).lower ∧ (cell12463 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12463 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12463 ⟨19,by decide⟩).lower ∧ (cell12463 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12463 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12463 ⟨20,by decide⟩).lower ∧ (cell12463 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12463 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12463 ⟨21,by decide⟩).lower ∧ (cell12463 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12463 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12463 ⟨22,by decide⟩).lower ∧ (cell12463 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12463 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12463 ⟨23,by decide⟩).lower ∧ (cell12463 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12463 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12463 ⟨24,by decide⟩).lower ∧ (cell12463 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12463 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12463 ⟨25,by decide⟩).lower ∧ (cell12463 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12463 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12463 ⟨26,by decide⟩).lower ∧ (cell12463 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12463 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12463 ⟨27,by decide⟩).lower ∧ (cell12463 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12463 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12463 ⟨28,by decide⟩).lower ∧ (cell12463 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12463 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12463 ⟨29,by decide⟩).lower ∧ (cell12463 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12463 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12463 ⟨30,by decide⟩).lower ∧ (cell12463 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12463 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12463 ⟨31,by decide⟩).lower ∧ (cell12463 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12463 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12463 ⟨32,by decide⟩).lower ∧ (cell12463 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12463 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12463 ⟨33,by decide⟩).lower ∧ (cell12463 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12463 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12463 ⟨34,by decide⟩).lower ∧ (cell12463 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12463 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12463 ⟨35,by decide⟩).lower ∧ (cell12463 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12463 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12463 ⟨36,by decide⟩).lower ∧ (cell12463 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12463 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12463 ⟨37,by decide⟩).lower ∧ (cell12463 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12463 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12463 ⟨38,by decide⟩).lower ∧ (cell12463 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12463 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12463 ⟨39,by decide⟩).lower ∧ (cell12463 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12463 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12463 ⟨40,by decide⟩).lower ∧ (cell12463 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12463 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12463 ⟨41,by decide⟩).lower ∧ (cell12463 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12463 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12463 ⟨42,by decide⟩).lower ∧ (cell12463 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12463 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12463 ⟨43,by decide⟩).lower ∧ (cell12463 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12463 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12463 ⟨44,by decide⟩).lower ∧ (cell12463 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12463 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12463 ⟨45,by decide⟩).lower ∧ (cell12463 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12463 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12463 ⟨46,by decide⟩).lower ∧ (cell12463 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12463 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12463 ⟨47,by decide⟩).lower ∧ (cell12463 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12463 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12463 ⟨48,by decide⟩).lower ∧ (cell12463 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12463 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12463 ⟨49,by decide⟩).lower ∧ (cell12463 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12463 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12463 ⟨50,by decide⟩).lower ∧ (cell12463 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12463 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12463 ⟨51,by decide⟩).lower ∧ (cell12463 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12463 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12463 ⟨52,by decide⟩).lower ∧ (cell12463 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12463 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12463 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12463 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12463,cell12463,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12463 i).lower ∧
    (cell12463 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12463 i).upper ≤ (0.532 : ℝ) ∧
    (cell12463 i).centre ≤ (0.1 : ℝ) ∧ (cell12463 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12463 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12463 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12463

/-! The local source numeric instances at 12463 have no network premises. -/
namespace BstLean.Part269.N12463
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12463)
open BstLean.Part268 (cell12463)

noncomputable def sourceNumerics12463 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12463 (cell12463 i)
      scalarRow12463.M scalarRow12463.H scalarRow12463.xi := by
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
    energy_allowance := scalarRow12463.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12463]
    centre_nonneg := (scalarRow12463.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12463])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12463
/-! Actual 12464 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12464
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12464 ≤ (1.036149642457 : ℝ) := by
  have hr : (111.642285895622 : ℝ) ≤ √(12464 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.642285895622 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12464 12464 (11 / 1000) ≤
    (0.008562052371 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12464) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.642285895622 : ℝ) ≤ √(12464 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12464)
  have hdiv : K / √(12464 : ℝ) ≤ K / 111.642285895622 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.642285895622 ≤ (0.008562052371 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12464.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12464 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12464 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12464 := gPlus_lower 12464
end BstLean.Part269.N12464

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12464
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036149642456 : ℝ) ≤ wn 12464 := by
  have hn : √(12464 : ℝ) ≤ 111.642285895623 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12464 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.642285895623 ≤ 2 / √(12464 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256734464 : ℝ) ≤ rhoBar 12464 BstLean.Part154.csC ∧
    rhoBar 12464 BstLean.Part154.csC ≤ 0.000256734861 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036149642456 : ℝ) / (1.295212 * 12464) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036149642457 : ℝ) / (1.29521 * 12464) := by gcongr
      _ ≤ (0.000256734861 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12464 BstLean.Part154.csC) ≤ 0.001027005357 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12464 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12464 BstLean.Part154.csC) (piBar (rhoBar 12464 BstLean.Part154.csC)) ≤ 0.000196095995 ∧
    cc1 (rhoBar 12464 BstLean.Part154.csC) (piBar (rhoBar 12464 BstLean.Part154.csC)) ≤ 0.000124777147 ∧
    cc2 (rhoBar 12464 BstLean.Part154.csC) ≤ 0.000072434046 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12464 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12464 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12464 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12464 BstLean.Part154.csC * nuR (rhoBar 12464 BstLean.Part154.csC)) ≤ 0.000513486200 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256734861 : ℝ) * 0.001027005357 := by gcongr
      _ ≤ (0.000513486200 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12464 BstLean.Part154.csC) * nuR (rhoBar 12464 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001027005357 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12464 BstLean.Part154.csC) * rhoBar 12464 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256734861 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256734861 / 2 + 0.399 * 0.001027005357 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196095995 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513486200 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124777147 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256734861 / 1.414213562 := by gcongr
      _ ≤ (0.000072434046 : ℝ) := by norm_num

end BstLean.Part269.N12464

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12464
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12464 BstLean.Part154.csC) (piBar (rhoBar 12464 BstLean.Part154.csC)) ≤ 1.66063E-7 := by
  have hr0 : 0 ≤ rhoBar 12464 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12464 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12464 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12464 BstLean.Part154.csC) (piBar (rhoBar 12464 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12464 BstLean.Part154.csC) (piBar (rhoBar 12464 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12464 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196095995 : ℝ) ^ 2 + 0.000124777147 ^ 2 + 3 * 0.000072434046 ^ 2 +
        2 * 0.797885 * 0.000196095995 * 0.000124777147 + 2 * 0.000196095995 * 0.000072434046 +
        4 * 0.797885 * 0.000124777147 * 0.000072434046 := by gcongr
    _ ≤ (1.66063E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12464 BstLean.Part154.csC Θ ≤ 0.002680841760 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12464 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12464 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12464 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12464 BstLean.Part154.csC) (piBar (rhoBar 12464 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12464 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036149642457 * 1.66063E-7 / (0.000256734464 : ℝ) := by gcongr
    _ ≤ 0.002680841760 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12464 BstLean.Part154.csC Θ ≤ 0.002975511838 + 0.000677403647 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12464 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12464 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12464 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036149642457 : ℝ) * ((2 * Θ * 0.000256734861 +
        (6863 / 10000) * 0.000256734861 * 12464 * 0.001027005357) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002975511838 + 0.000677403647 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12464 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12464 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12464 0.011 Θ ∧ gammaRatio 12464 0.011 Θ ≤ 0.000088258807 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12464 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036149642457 : ℝ) * 0.525 / ((1 - 0.011) * 12464) := by gcongr
      _ ≤ (0.000088258807 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12464 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12464 0.011 Θ) :=
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
    badAllowance 12464 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12464 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12464 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12464 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12464 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12464 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12464 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12464 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12464 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12464 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12464 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036149642457 : ℝ) * 12464 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12464 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003791886584 + 0.003358245407 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12464

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12464
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12464 BstLean.Part154.csC) (piBar (rhoBar 12464 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12464 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12464 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12464 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12464 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12464 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12464 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12464 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12464 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12464 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12464 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12464 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12464 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12464 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12464 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052984278878 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12464) ≤ 0.010697000438 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12464 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036149642457)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010697000438 + 2 * 0.737676 / 12464) := by gcongr
    _ ≤ (0.052984278878 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12464 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12464

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12464
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492693589 : ℝ) ≤ plow 12464 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12464) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053061565423)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407441924) : eMP 12464 0.011 xi bn ≤ 0.001211347986 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12464 : ℝ) * (1 - 0.011))) ≤ 0.000598912443 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001407441924 / (12464 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598912443 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598912443 : ℝ) + 3.141593 * 0.053061565423 / (12464 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001211347986 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053061565423)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407441924) : PiBarMP 12464 12 0.011 xi bn ≤ 0.162786221963 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12464 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037515888954 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.026555382034 : ℝ) ≤ √((12464 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.642285895622 : ℝ) ≤ √(12464 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12464) ≤ 0.124795082356 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037515888954 + 0.053061565423 * 1.772454 / (2 * (111.026555382034 : ℝ))) * (1 + 0.001211347986) +
        8 / (12464 * 111.642285895622) + 0.124795082356 := by gcongr
    _ ≤ (0.162786221963 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053061565423)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407441924) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283335240290) :
    parallelOracle 12464 0.011 xi bn cd ≤ 0.163796230489 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12464 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12464 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492693589 : ℝ) ≤ plow 12464 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.642285895622 : ℝ) ≤ √(12464 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283335240290 : ℝ) / (2 * 0.560492693589 * 111.642285895622)) * 0.162786221963 +
        0.283335240290 ^ 2 / (2 * 0.560492693589 * 111.642285895622) := by gcongr
    _ ≤ (0.163796230489 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053061565423) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407441924)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283335240290) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12464 12464 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492693589 : ℝ) ≤ plow 12464 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.642285895622 : ℝ) ≤ √(12464 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12464 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12464 Θ 1.22 ≤ 0.011878120279 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.642285895622 := by gcongr <;> linarith
      _ ≤ (0.011878120279 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12464 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12464 12464 0.011 ≤ 0.008562052371 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12464 12464 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12464 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12464 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12464 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12464 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163796230489 + 0.011878120279 + (0.008562052371 : ℝ) *
        (1 + 2 * (0.283335240290 + 0.011878120279) / (0.560492693589 * 111.642285895622))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12464]

end BstLean.Part269.N12464

/-! The original eight local profiles supply actual 12464 moment certificates. -/
namespace BstLean.Part269.N12464
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12464 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12464 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12464 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053061565423 ∧
    0 ≤ bN 12464 BstLean.Part154.csC (groupTheta g) ∧ bN 12464 BstLean.Part154.csC (groupTheta g) ≤ 0.001407441924 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12464 12464 0.011
      (momentAllowance 12464 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12464 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12464 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12464 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12464 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12464 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230350961412 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12464 0.011
      (momentAllowance 12464 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12464 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12464
/-! The actual computed-centre upper energy formula at 12464. -/
namespace BstLean.Part269.N12464
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12464

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12464
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12464)
open BstLean.Part268 (cell12464)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086211287889
  | 2 => 0.087168057883
  | 3 => 0.088125134975
  | 4 => 0.089084427078
  | 5 => 0.090048224094
  | 6 => 0.091019252285
  | 7 => 0.092000733329
  | 8 => 0.092996448036
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12464 12464 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12464 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003795409572 + 0.003362150420 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S4.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12464

/-! Actual upper energy certificates on all 43 source endpoints at 12464. -/
namespace BstLean.Part269.N12464
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12464)
open BstLean.Part268 (cell12464)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12464 (gMinus 12464) (1 - (cell12464 i).lower) ≤ 1 ∧
    energyUpper 12464 (gMinus 12464) (BstLean.Part211.gPlus 12464)
      (finiteEnergy 12464 12464 0.011) (1 - (cell12464 i).lower) ≤
      (cell12464 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨10,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨11,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨12,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨13,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨14,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨15,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨16,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨17,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨18,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨19,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨20,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨21,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨22,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨23,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨24,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨25,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨26,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨27,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨28,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨29,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨30,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨31,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨32,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨33,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨34,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨35,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨36,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨37,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨38,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨39,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨40,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨41,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨42,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨43,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨44,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨45,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨46,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨47,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨48,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨49,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨50,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨51,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12464) (by norm_num)
        (q := 1 - (cell12464 ⟨52,by decide⟩).lower)
        (by norm_num [cell12464]) (by norm_num [cell12464])
      exact ⟨E.1,E.2.trans (by norm_num [cell12464])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12464

/-! Source-cell containment and simple scalar guards at 12464. -/
namespace BstLean.Part269.N12464
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12464)
open BstLean.Part268 (cell12464)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12464 ⟨10,by decide⟩).lower ∧ (cell12464 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12464 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12464 ⟨11,by decide⟩).lower ∧ (cell12464 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12464 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12464 ⟨12,by decide⟩).lower ∧ (cell12464 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12464 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12464 ⟨13,by decide⟩).lower ∧ (cell12464 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12464 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12464 ⟨14,by decide⟩).lower ∧ (cell12464 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12464 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12464 ⟨15,by decide⟩).lower ∧ (cell12464 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12464 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12464 ⟨16,by decide⟩).lower ∧ (cell12464 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12464 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12464 ⟨17,by decide⟩).lower ∧ (cell12464 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12464 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12464 ⟨18,by decide⟩).lower ∧ (cell12464 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12464 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12464 ⟨19,by decide⟩).lower ∧ (cell12464 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12464 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12464 ⟨20,by decide⟩).lower ∧ (cell12464 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12464 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12464 ⟨21,by decide⟩).lower ∧ (cell12464 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12464 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12464 ⟨22,by decide⟩).lower ∧ (cell12464 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12464 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12464 ⟨23,by decide⟩).lower ∧ (cell12464 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12464 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12464 ⟨24,by decide⟩).lower ∧ (cell12464 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12464 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12464 ⟨25,by decide⟩).lower ∧ (cell12464 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12464 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12464 ⟨26,by decide⟩).lower ∧ (cell12464 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12464 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12464 ⟨27,by decide⟩).lower ∧ (cell12464 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12464 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12464 ⟨28,by decide⟩).lower ∧ (cell12464 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12464 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12464 ⟨29,by decide⟩).lower ∧ (cell12464 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12464 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12464 ⟨30,by decide⟩).lower ∧ (cell12464 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12464 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12464 ⟨31,by decide⟩).lower ∧ (cell12464 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12464 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12464 ⟨32,by decide⟩).lower ∧ (cell12464 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12464 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12464 ⟨33,by decide⟩).lower ∧ (cell12464 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12464 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12464 ⟨34,by decide⟩).lower ∧ (cell12464 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12464 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12464 ⟨35,by decide⟩).lower ∧ (cell12464 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12464 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12464 ⟨36,by decide⟩).lower ∧ (cell12464 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12464 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12464 ⟨37,by decide⟩).lower ∧ (cell12464 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12464 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12464 ⟨38,by decide⟩).lower ∧ (cell12464 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12464 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12464 ⟨39,by decide⟩).lower ∧ (cell12464 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12464 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12464 ⟨40,by decide⟩).lower ∧ (cell12464 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12464 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12464 ⟨41,by decide⟩).lower ∧ (cell12464 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12464 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12464 ⟨42,by decide⟩).lower ∧ (cell12464 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12464 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12464 ⟨43,by decide⟩).lower ∧ (cell12464 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12464 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12464 ⟨44,by decide⟩).lower ∧ (cell12464 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12464 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12464 ⟨45,by decide⟩).lower ∧ (cell12464 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12464 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12464 ⟨46,by decide⟩).lower ∧ (cell12464 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12464 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12464 ⟨47,by decide⟩).lower ∧ (cell12464 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12464 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12464 ⟨48,by decide⟩).lower ∧ (cell12464 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12464 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12464 ⟨49,by decide⟩).lower ∧ (cell12464 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12464 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12464 ⟨50,by decide⟩).lower ∧ (cell12464 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12464 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12464 ⟨51,by decide⟩).lower ∧ (cell12464 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12464 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12464 ⟨52,by decide⟩).lower ∧ (cell12464 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12464 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12464 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12464 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12464,cell12464,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12464 i).lower ∧
    (cell12464 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12464 i).upper ≤ (0.532 : ℝ) ∧
    (cell12464 i).centre ≤ (0.1 : ℝ) ∧ (cell12464 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12464 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12464 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12464

/-! The local source numeric instances at 12464 have no network premises. -/
namespace BstLean.Part269.N12464
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12464)
open BstLean.Part268 (cell12464)

noncomputable def sourceNumerics12464 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12464 (cell12464 i)
      scalarRow12464.M scalarRow12464.H scalarRow12464.xi := by
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
    energy_allowance := scalarRow12464.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12464]
    centre_nonneg := (scalarRow12464.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12464])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12464
/-! Actual 12465 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12465
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12465 ≤ (1.036148179510 : ℝ) := by
  have hr : (111.646764395570 : ℝ) ≤ √(12465 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.646764395570 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12465 12465 (11 / 1000) ≤
    (0.008561708918 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12465) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.646764395570 : ℝ) ≤ √(12465 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12465)
  have hdiv : K / √(12465 : ℝ) ≤ K / 111.646764395570 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.646764395570 ≤ (0.008561708918 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12465.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12465 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12465 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12465 := gPlus_lower 12465
end BstLean.Part269.N12465

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12465
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036148179509 : ℝ) ≤ wn 12465 := by
  have hn : √(12465 : ℝ) ≤ 111.646764395571 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12465 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.646764395571 ≤ 2 / √(12465 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256713505 : ℝ) ≤ rhoBar 12465 BstLean.Part154.csC ∧
    rhoBar 12465 BstLean.Part154.csC ≤ 0.000256713902 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036148179509 : ℝ) / (1.295212 * 12465) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036148179510 : ℝ) / (1.29521 * 12465) := by gcongr
      _ ≤ (0.000256713902 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12465 BstLean.Part154.csC) ≤ 0.001026921511 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12465 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12465 BstLean.Part154.csC) (piBar (rhoBar 12465 BstLean.Part154.csC)) ≤ 0.000196079985 ∧
    cc1 (rhoBar 12465 BstLean.Part154.csC) (piBar (rhoBar 12465 BstLean.Part154.csC)) ≤ 0.000124766961 ∧
    cc2 (rhoBar 12465 BstLean.Part154.csC) ≤ 0.000072428133 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12465 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12465 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12465 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12465 BstLean.Part154.csC * nuR (rhoBar 12465 BstLean.Part154.csC)) ≤ 0.000513444280 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256713902 : ℝ) * 0.001026921511 := by gcongr
      _ ≤ (0.000513444280 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12465 BstLean.Part154.csC) * nuR (rhoBar 12465 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001026921511 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12465 BstLean.Part154.csC) * rhoBar 12465 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256713902 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256713902 / 2 + 0.399 * 0.001026921511 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196079985 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513444280 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124766961 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256713902 / 1.414213562 := by gcongr
      _ ≤ (0.000072428133 : ℝ) := by norm_num

end BstLean.Part269.N12465

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12465
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12465 BstLean.Part154.csC) (piBar (rhoBar 12465 BstLean.Part154.csC)) ≤ 1.66036E-7 := by
  have hr0 : 0 ≤ rhoBar 12465 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12465 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12465 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12465 BstLean.Part154.csC) (piBar (rhoBar 12465 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12465 BstLean.Part154.csC) (piBar (rhoBar 12465 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12465 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196079985 : ℝ) ^ 2 + 0.000124766961 ^ 2 + 3 * 0.000072428133 ^ 2 +
        2 * 0.797885 * 0.000196079985 * 0.000124766961 + 2 * 0.000196079985 * 0.000072428133 +
        4 * 0.797885 * 0.000124766961 * 0.000072428133 := by gcongr
    _ ≤ (1.66036E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12465 BstLean.Part154.csC Θ ≤ 0.002680620938 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12465 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12465 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12465 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12465 BstLean.Part154.csC) (piBar (rhoBar 12465 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12465 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036148179510 * 1.66036E-7 / (0.000256713505 : ℝ) := by gcongr
    _ ≤ 0.002680620938 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12465 BstLean.Part154.csC Θ ≤ 0.002975260511 + 0.000677347389 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12465 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12465 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12465 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036148179510 : ℝ) * ((2 * Θ * 0.000256713902 +
        (6863 / 10000) * 0.000256713902 * 12465 * 0.001026921511) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002975260511 + 0.000677347389 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12465 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12465 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12465 0.011 Θ ∧ gammaRatio 12465 0.011 Θ ≤ 0.000088251602 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12465 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036148179510 : ℝ) * 0.525 / ((1 - 0.011) * 12465) := by gcongr
      _ ≤ (0.000088251602 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12465 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12465 0.011 Θ) :=
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
    badAllowance 12465 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12465 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12465 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12465 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12465 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12465 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12465 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12465 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12465 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12465 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12465 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036148179510 : ℝ) * 12465 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12465 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003791635257 + 0.003357968327 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12465

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12465
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12465 BstLean.Part154.csC) (piBar (rhoBar 12465 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12465 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12465 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12465 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12465 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12465 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12465 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12465 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12465 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12465 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12465 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12465 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12465 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12465 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12465 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052982130253 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12465) ≤ 0.010696571348 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12465 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036148179510)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010696571348 + 2 * 0.737676 / 12465) := by gcongr
    _ ≤ (0.052982130253 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12465 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12465

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12465
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492740537 : ℝ) ≤ plow 12465 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12465) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053061168629)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407325993) : eMP 12465 0.011 xi bn ≤ 0.001211249420 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12465 : ℝ) * (1 - 0.011))) ≤ 0.000598863753 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001407325993 / (12465 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598863753 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598863753 : ℝ) + 3.141593 * 0.053061168629 / (12465 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001211249420 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053061168629)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407325993) : PiBarMP 12465 12 0.011 xi bn ≤ 0.162779644436 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12465 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037514343831 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.031009182119 : ℝ) ≤ √((12465 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.646764395570 : ℝ) ≤ √(12465 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12465) ≤ 0.124790076436 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037514343831 + 0.053061168629 * 1.772454 / (2 * (111.031009182119 : ℝ))) * (1 + 0.001211249420) +
        8 / (12465 * 111.646764395570) + 0.124790076436 := by gcongr
    _ ≤ (0.162779644436 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053061168629)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407325993) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283332230382) :
    parallelOracle 12465 0.011 xi bn cd ≤ 0.163789579929 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12465 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12465 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492740537 : ℝ) ≤ plow 12465 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.646764395570 : ℝ) ≤ √(12465 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283332230382 : ℝ) / (2 * 0.560492740537 * 111.646764395570)) * 0.162779644436 +
        0.283332230382 ^ 2 / (2 * 0.560492740537 * 111.646764395570) := by gcongr
    _ ≤ (0.163789579929 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053061168629) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407325993)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283332230382) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12465 12465 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492740537 : ℝ) ≤ plow 12465 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.646764395570 : ℝ) ≤ √(12465 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12465 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12465 Θ 1.22 ≤ 0.011877643810 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.646764395570 := by gcongr <;> linarith
      _ ≤ (0.011877643810 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12465 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12465 12465 0.011 ≤ 0.008561708918 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12465 12465 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12465 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12465 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12465 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12465 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163789579929 + 0.011877643810 + (0.008561708918 : ℝ) *
        (1 + 2 * (0.283332230382 + 0.011877643810) / (0.560492740537 * 111.646764395570))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12465]

end BstLean.Part269.N12465

/-! The original eight local profiles supply actual 12465 moment certificates. -/
namespace BstLean.Part269.N12465
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12465 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12465 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12465 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053061168629 ∧
    0 ≤ bN 12465 BstLean.Part154.csC (groupTheta g) ∧ bN 12465 BstLean.Part154.csC (groupTheta g) ≤ 0.001407325993 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12465 12465 0.011
      (momentAllowance 12465 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12465 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12465 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12465 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12465 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12465 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230350100129 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12465 0.011
      (momentAllowance 12465 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12465 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12465
/-! The actual computed-centre upper energy formula at 12465. -/
namespace BstLean.Part269.N12465
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12465

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12465
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12465)
open BstLean.Part268 (cell12465)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086208082538
  | 2 => 0.087164786690
  | 3 => 0.088121787252
  | 4 => 0.089080989759
  | 5 => 0.090044681336
  | 6 => 0.091015585013
  | 7 => 0.091996918738
  | 8 => 0.092992459036
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12465 12465 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12465 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003795409572 + 0.003362150420 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S4.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12465

/-! Actual upper energy certificates on all 43 source endpoints at 12465. -/
namespace BstLean.Part269.N12465
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12465)
open BstLean.Part268 (cell12465)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12465 (gMinus 12465) (1 - (cell12465 i).lower) ≤ 1 ∧
    energyUpper 12465 (gMinus 12465) (BstLean.Part211.gPlus 12465)
      (finiteEnergy 12465 12465 0.011) (1 - (cell12465 i).lower) ≤
      (cell12465 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨10,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨11,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨12,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨13,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨14,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨15,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨16,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨17,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨18,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨19,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨20,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨21,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨22,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨23,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨24,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨25,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨26,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨27,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨28,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨29,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨30,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨31,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨32,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨33,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨34,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨35,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨36,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨37,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨38,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨39,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨40,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨41,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨42,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨43,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨44,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨45,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨46,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨47,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨48,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨49,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨50,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨51,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12465) (by norm_num)
        (q := 1 - (cell12465 ⟨52,by decide⟩).lower)
        (by norm_num [cell12465]) (by norm_num [cell12465])
      exact ⟨E.1,E.2.trans (by norm_num [cell12465])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12465

/-! Source-cell containment and simple scalar guards at 12465. -/
namespace BstLean.Part269.N12465
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12465)
open BstLean.Part268 (cell12465)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12465 ⟨10,by decide⟩).lower ∧ (cell12465 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12465 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12465 ⟨11,by decide⟩).lower ∧ (cell12465 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12465 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12465 ⟨12,by decide⟩).lower ∧ (cell12465 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12465 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12465 ⟨13,by decide⟩).lower ∧ (cell12465 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12465 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12465 ⟨14,by decide⟩).lower ∧ (cell12465 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12465 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12465 ⟨15,by decide⟩).lower ∧ (cell12465 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12465 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12465 ⟨16,by decide⟩).lower ∧ (cell12465 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12465 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12465 ⟨17,by decide⟩).lower ∧ (cell12465 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12465 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12465 ⟨18,by decide⟩).lower ∧ (cell12465 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12465 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12465 ⟨19,by decide⟩).lower ∧ (cell12465 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12465 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12465 ⟨20,by decide⟩).lower ∧ (cell12465 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12465 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12465 ⟨21,by decide⟩).lower ∧ (cell12465 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12465 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12465 ⟨22,by decide⟩).lower ∧ (cell12465 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12465 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12465 ⟨23,by decide⟩).lower ∧ (cell12465 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12465 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12465 ⟨24,by decide⟩).lower ∧ (cell12465 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12465 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12465 ⟨25,by decide⟩).lower ∧ (cell12465 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12465 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12465 ⟨26,by decide⟩).lower ∧ (cell12465 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12465 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12465 ⟨27,by decide⟩).lower ∧ (cell12465 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12465 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12465 ⟨28,by decide⟩).lower ∧ (cell12465 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12465 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12465 ⟨29,by decide⟩).lower ∧ (cell12465 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12465 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12465 ⟨30,by decide⟩).lower ∧ (cell12465 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12465 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12465 ⟨31,by decide⟩).lower ∧ (cell12465 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12465 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12465 ⟨32,by decide⟩).lower ∧ (cell12465 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12465 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12465 ⟨33,by decide⟩).lower ∧ (cell12465 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12465 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12465 ⟨34,by decide⟩).lower ∧ (cell12465 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12465 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12465 ⟨35,by decide⟩).lower ∧ (cell12465 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12465 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12465 ⟨36,by decide⟩).lower ∧ (cell12465 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12465 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12465 ⟨37,by decide⟩).lower ∧ (cell12465 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12465 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12465 ⟨38,by decide⟩).lower ∧ (cell12465 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12465 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12465 ⟨39,by decide⟩).lower ∧ (cell12465 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12465 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12465 ⟨40,by decide⟩).lower ∧ (cell12465 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12465 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12465 ⟨41,by decide⟩).lower ∧ (cell12465 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12465 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12465 ⟨42,by decide⟩).lower ∧ (cell12465 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12465 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12465 ⟨43,by decide⟩).lower ∧ (cell12465 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12465 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12465 ⟨44,by decide⟩).lower ∧ (cell12465 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12465 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12465 ⟨45,by decide⟩).lower ∧ (cell12465 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12465 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12465 ⟨46,by decide⟩).lower ∧ (cell12465 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12465 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12465 ⟨47,by decide⟩).lower ∧ (cell12465 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12465 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12465 ⟨48,by decide⟩).lower ∧ (cell12465 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12465 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12465 ⟨49,by decide⟩).lower ∧ (cell12465 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12465 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12465 ⟨50,by decide⟩).lower ∧ (cell12465 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12465 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12465 ⟨51,by decide⟩).lower ∧ (cell12465 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12465 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12465 ⟨52,by decide⟩).lower ∧ (cell12465 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12465 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12465 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12465 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12465,cell12465,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12465 i).lower ∧
    (cell12465 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12465 i).upper ≤ (0.532 : ℝ) ∧
    (cell12465 i).centre ≤ (0.1 : ℝ) ∧ (cell12465 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12465 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12465 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12465

/-! The local source numeric instances at 12465 have no network premises. -/
namespace BstLean.Part269.N12465
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12465)
open BstLean.Part268 (cell12465)

noncomputable def sourceNumerics12465 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12465 (cell12465 i)
      scalarRow12465.M scalarRow12465.H scalarRow12465.xi := by
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
    energy_allowance := scalarRow12465.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12465]
    centre_nonneg := (scalarRow12465.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12465])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12465
/-! Actual 12466 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12466
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12466 ≤ (1.036146716739 : ℝ) := by
  have hr : (111.651242715878 : ℝ) ≤ √(12466 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.651242715878 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12466 12466 (11 / 1000) ≤
    (0.008561365506 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12466) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.651242715878 : ℝ) ≤ √(12466 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12466)
  have hdiv : K / √(12466 : ℝ) ≤ K / 111.651242715878 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.651242715878 ≤ (0.008561365506 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12466.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12466 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12466 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12466 := gPlus_lower 12466
end BstLean.Part269.N12466

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12466
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036146716738 : ℝ) ≤ wn 12466 := by
  have hn : √(12466 : ℝ) ≤ 111.651242715879 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12466 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.651242715879 ≤ 2 / √(12466 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256692550 : ℝ) ≤ rhoBar 12466 BstLean.Part154.csC ∧
    rhoBar 12466 BstLean.Part154.csC ≤ 0.000256692947 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036146716738 : ℝ) / (1.295212 * 12466) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036146716739 : ℝ) / (1.29521 * 12466) := by gcongr
      _ ≤ (0.000256692947 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12466 BstLean.Part154.csC) ≤ 0.001026837680 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12466 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12466 BstLean.Part154.csC) (piBar (rhoBar 12466 BstLean.Part154.csC)) ≤ 0.000196063979 ∧
    cc1 (rhoBar 12466 BstLean.Part154.csC) (piBar (rhoBar 12466 BstLean.Part154.csC)) ≤ 0.000124756776 ∧
    cc2 (rhoBar 12466 BstLean.Part154.csC) ≤ 0.000072422221 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12466 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12466 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12466 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12466 BstLean.Part154.csC * nuR (rhoBar 12466 BstLean.Part154.csC)) ≤ 0.000513402367 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256692947 : ℝ) * 0.001026837680 := by gcongr
      _ ≤ (0.000513402367 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12466 BstLean.Part154.csC) * nuR (rhoBar 12466 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001026837680 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12466 BstLean.Part154.csC) * rhoBar 12466 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256692947 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256692947 / 2 + 0.399 * 0.001026837680 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196063979 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513402367 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124756776 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256692947 / 1.414213562 := by gcongr
      _ ≤ (0.000072422221 : ℝ) := by norm_num

end BstLean.Part269.N12466

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12466
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12466 BstLean.Part154.csC) (piBar (rhoBar 12466 BstLean.Part154.csC)) ≤ 1.66009E-7 := by
  have hr0 : 0 ≤ rhoBar 12466 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12466 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12466 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12466 BstLean.Part154.csC) (piBar (rhoBar 12466 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12466 BstLean.Part154.csC) (piBar (rhoBar 12466 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12466 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196063979 : ℝ) ^ 2 + 0.000124756776 ^ 2 + 3 * 0.000072422221 ^ 2 +
        2 * 0.797885 * 0.000196063979 * 0.000124756776 + 2 * 0.000196063979 * 0.000072422221 +
        4 * 0.797885 * 0.000124756776 * 0.000072422221 := by gcongr
    _ ≤ (1.66009E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12466 BstLean.Part154.csC Θ ≤ 0.002680400040 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12466 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12466 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12466 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12466 BstLean.Part154.csC) (piBar (rhoBar 12466 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12466 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036146716739 * 1.66009E-7 / (0.000256692550 : ℝ) := by gcongr
    _ ≤ 0.002680400040 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12466 BstLean.Part154.csC Θ ≤ 0.002975009237 + 0.000677291143 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12466 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12466 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12466 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036146716739 : ℝ) * ((2 * Θ * 0.000256692947 +
        (6863 / 10000) * 0.000256692947 * 12466 * 0.001026837680) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002975009237 + 0.000677291143 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12466 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12466 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12466 0.011 Θ ∧ gammaRatio 12466 0.011 Θ ≤ 0.000088244398 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12466 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036146716739 : ℝ) * 0.525 / ((1 - 0.011) * 12466) := by gcongr
      _ ≤ (0.000088244398 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12466 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12466 0.011 Θ) :=
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
    badAllowance 12466 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12466 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12466 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12466 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12466 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12466 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12466 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12466 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12466 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12466 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12466 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036146716739 : ℝ) * 12466 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12466 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003791383983 + 0.003357691183 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12466

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12466
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12466 BstLean.Part154.csC) (piBar (rhoBar 12466 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12466 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12466 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12466 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12466 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12466 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12466 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12466 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12466 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12466 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12466 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12466 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12466 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12466 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12466 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052979981886 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12466) ≤ 0.010696142309 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12466 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036146716739)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010696142309 + 2 * 0.737676 / 12466) := by gcongr
    _ ≤ (0.052979981886 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12466 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12466

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12466
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492787477 : ℝ) ≤ plow 12466 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12466) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053060771855)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407210021) : eMP 12466 0.011 xi bn ≤ 0.001211150846 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12466 : ℝ) * (1 - 0.011))) ≤ 0.000598815059 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001407210021 / (12466 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598815059 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598815059 : ℝ) + 3.141593 * 0.053060771855 / (12466 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001211150846 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053060771855)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407210021) : PiBarMP 12466 12 0.011 xi bn ≤ 0.162773066903 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12466 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037512798097 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.035462803556 : ℝ) ≤ √((12466 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.651242715878 : ℝ) ≤ √(12466 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12466) ≤ 0.124785071119 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037512798097 + 0.053060771855 * 1.772454 / (2 * (111.035462803556 : ℝ))) * (1 + 0.001211150846) +
        8 / (12466 * 111.651242715878) + 0.124785071119 := by gcongr
    _ ≤ (0.162773066903 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053060771855)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407210021) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283329220772) :
    parallelOracle 12466 0.011 xi bn cd ≤ 0.163782929373 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12466 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12466 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492787477 : ℝ) ≤ plow 12466 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.651242715878 : ℝ) ≤ √(12466 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283329220772 : ℝ) / (2 * 0.560492787477 * 111.651242715878)) * 0.162773066903 +
        0.283329220772 ^ 2 / (2 * 0.560492787477 * 111.651242715878) := by gcongr
    _ ≤ (0.163782929373 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053060771855) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407210021)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283329220772) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12466 12466 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492787477 : ℝ) ≤ plow 12466 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.651242715878 : ℝ) ≤ √(12466 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12466 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12466 Θ 1.22 ≤ 0.011877167399 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.651242715878 := by gcongr <;> linarith
      _ ≤ (0.011877167399 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12466 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12466 12466 0.011 ≤ 0.008561365506 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12466 12466 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12466 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12466 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12466 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12466 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163782929373 + 0.011877167399 + (0.008561365506 : ℝ) *
        (1 + 2 * (0.283329220772 + 0.011877167399) / (0.560492787477 * 111.651242715878))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12466]

end BstLean.Part269.N12466

/-! The original eight local profiles supply actual 12466 moment certificates. -/
namespace BstLean.Part269.N12466
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12466 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12466 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12466 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053060771855 ∧
    0 ≤ bN 12466 BstLean.Part154.csC (groupTheta g) ∧ bN 12466 BstLean.Part154.csC (groupTheta g) ≤ 0.001407210021 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12466 12466 0.011
      (momentAllowance 12466 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12466 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12466 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12466 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12466 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12466 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230349238886 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12466 0.011
      (momentAllowance 12466 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12466 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12466
/-! The actual computed-centre upper energy formula at 12466. -/
namespace BstLean.Part269.N12466
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12466

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12466
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12466)
open BstLean.Part268 (cell12466)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086204878572
  | 2 => 0.087161516944
  | 3 => 0.088118441049
  | 4 => 0.089077554053
  | 5 => 0.090041140301
  | 6 => 0.091011919600
  | 7 => 0.091993106169
  | 8 => 0.092988472254
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12466 12466 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12466 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003795409572 + 0.003362150420 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S4.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12466

/-! Actual upper energy certificates on all 43 source endpoints at 12466. -/
namespace BstLean.Part269.N12466
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12466)
open BstLean.Part268 (cell12466)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12466 (gMinus 12466) (1 - (cell12466 i).lower) ≤ 1 ∧
    energyUpper 12466 (gMinus 12466) (BstLean.Part211.gPlus 12466)
      (finiteEnergy 12466 12466 0.011) (1 - (cell12466 i).lower) ≤
      (cell12466 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨10,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨11,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨12,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨13,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨14,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨15,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨16,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨17,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨18,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨19,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨20,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨21,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨22,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨23,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨24,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨25,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨26,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨27,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨28,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨29,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨30,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨31,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨32,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨33,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨34,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨35,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨36,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨37,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨38,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨39,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨40,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨41,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨42,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨43,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨44,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨45,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨46,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨47,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨48,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨49,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨50,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨51,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12466) (by norm_num)
        (q := 1 - (cell12466 ⟨52,by decide⟩).lower)
        (by norm_num [cell12466]) (by norm_num [cell12466])
      exact ⟨E.1,E.2.trans (by norm_num [cell12466])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12466

/-! Source-cell containment and simple scalar guards at 12466. -/
namespace BstLean.Part269.N12466
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12466)
open BstLean.Part268 (cell12466)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12466 ⟨10,by decide⟩).lower ∧ (cell12466 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12466 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12466 ⟨11,by decide⟩).lower ∧ (cell12466 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12466 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12466 ⟨12,by decide⟩).lower ∧ (cell12466 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12466 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12466 ⟨13,by decide⟩).lower ∧ (cell12466 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12466 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12466 ⟨14,by decide⟩).lower ∧ (cell12466 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12466 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12466 ⟨15,by decide⟩).lower ∧ (cell12466 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12466 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12466 ⟨16,by decide⟩).lower ∧ (cell12466 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12466 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12466 ⟨17,by decide⟩).lower ∧ (cell12466 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12466 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12466 ⟨18,by decide⟩).lower ∧ (cell12466 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12466 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12466 ⟨19,by decide⟩).lower ∧ (cell12466 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12466 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12466 ⟨20,by decide⟩).lower ∧ (cell12466 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12466 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12466 ⟨21,by decide⟩).lower ∧ (cell12466 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12466 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12466 ⟨22,by decide⟩).lower ∧ (cell12466 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12466 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12466 ⟨23,by decide⟩).lower ∧ (cell12466 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12466 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12466 ⟨24,by decide⟩).lower ∧ (cell12466 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12466 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12466 ⟨25,by decide⟩).lower ∧ (cell12466 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12466 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12466 ⟨26,by decide⟩).lower ∧ (cell12466 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12466 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12466 ⟨27,by decide⟩).lower ∧ (cell12466 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12466 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12466 ⟨28,by decide⟩).lower ∧ (cell12466 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12466 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12466 ⟨29,by decide⟩).lower ∧ (cell12466 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12466 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12466 ⟨30,by decide⟩).lower ∧ (cell12466 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12466 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12466 ⟨31,by decide⟩).lower ∧ (cell12466 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12466 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12466 ⟨32,by decide⟩).lower ∧ (cell12466 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12466 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12466 ⟨33,by decide⟩).lower ∧ (cell12466 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12466 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12466 ⟨34,by decide⟩).lower ∧ (cell12466 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12466 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12466 ⟨35,by decide⟩).lower ∧ (cell12466 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12466 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12466 ⟨36,by decide⟩).lower ∧ (cell12466 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12466 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12466 ⟨37,by decide⟩).lower ∧ (cell12466 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12466 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12466 ⟨38,by decide⟩).lower ∧ (cell12466 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12466 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12466 ⟨39,by decide⟩).lower ∧ (cell12466 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12466 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12466 ⟨40,by decide⟩).lower ∧ (cell12466 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12466 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12466 ⟨41,by decide⟩).lower ∧ (cell12466 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12466 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12466 ⟨42,by decide⟩).lower ∧ (cell12466 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12466 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12466 ⟨43,by decide⟩).lower ∧ (cell12466 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12466 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12466 ⟨44,by decide⟩).lower ∧ (cell12466 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12466 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12466 ⟨45,by decide⟩).lower ∧ (cell12466 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12466 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12466 ⟨46,by decide⟩).lower ∧ (cell12466 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12466 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12466 ⟨47,by decide⟩).lower ∧ (cell12466 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12466 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12466 ⟨48,by decide⟩).lower ∧ (cell12466 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12466 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12466 ⟨49,by decide⟩).lower ∧ (cell12466 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12466 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12466 ⟨50,by decide⟩).lower ∧ (cell12466 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12466 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12466 ⟨51,by decide⟩).lower ∧ (cell12466 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12466 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12466 ⟨52,by decide⟩).lower ∧ (cell12466 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12466 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12466 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12466 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12466,cell12466,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12466 i).lower ∧
    (cell12466 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12466 i).upper ≤ (0.532 : ℝ) ∧
    (cell12466 i).centre ≤ (0.1 : ℝ) ∧ (cell12466 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12466 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12466 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12466

/-! The local source numeric instances at 12466 have no network premises. -/
namespace BstLean.Part269.N12466
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12466)
open BstLean.Part268 (cell12466)

noncomputable def sourceNumerics12466 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12466 (cell12466 i)
      scalarRow12466.M scalarRow12466.H scalarRow12466.xi := by
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
    energy_allowance := scalarRow12466.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12466]
    centre_nonneg := (scalarRow12466.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12466])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12466
/-! Actual 12467 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12467
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12467 ≤ (1.036145254146 : ℝ) := by
  have hr : (111.655720856568 : ℝ) ≤ √(12467 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.655720856568 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12467 12467 (11 / 1000) ≤
    (0.008561022135 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12467) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.655720856568 : ℝ) ≤ √(12467 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12467)
  have hdiv : K / √(12467 : ℝ) ≤ K / 111.655720856568 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.655720856568 ≤ (0.008561022135 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12467.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12467 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12467 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12467 := gPlus_lower 12467
end BstLean.Part269.N12467

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12467
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036145254145 : ℝ) ≤ wn 12467 := by
  have hn : √(12467 : ℝ) ≤ 111.655720856569 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12467 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.655720856569 ≤ 2 / √(12467 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256671598 : ℝ) ≤ rhoBar 12467 BstLean.Part154.csC ∧
    rhoBar 12467 BstLean.Part154.csC ≤ 0.000256671995 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036145254145 : ℝ) / (1.295212 * 12467) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036145254146 : ℝ) / (1.29521 * 12467) := by gcongr
      _ ≤ (0.000256671995 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12467 BstLean.Part154.csC) ≤ 0.001026753861 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12467 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12467 BstLean.Part154.csC) (piBar (rhoBar 12467 BstLean.Part154.csC)) ≤ 0.000196047975 ∧
    cc1 (rhoBar 12467 BstLean.Part154.csC) (piBar (rhoBar 12467 BstLean.Part154.csC)) ≤ 0.000124746592 ∧
    cc2 (rhoBar 12467 BstLean.Part154.csC) ≤ 0.000072416309 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12467 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12467 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12467 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12467 BstLean.Part154.csC * nuR (rhoBar 12467 BstLean.Part154.csC)) ≤ 0.000513360460 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256671995 : ℝ) * 0.001026753861 := by gcongr
      _ ≤ (0.000513360460 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12467 BstLean.Part154.csC) * nuR (rhoBar 12467 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001026753861 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12467 BstLean.Part154.csC) * rhoBar 12467 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256671995 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256671995 / 2 + 0.399 * 0.001026753861 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196047975 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513360460 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124746592 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256671995 / 1.414213562 := by gcongr
      _ ≤ (0.000072416309 : ℝ) := by norm_num

end BstLean.Part269.N12467

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12467
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12467 BstLean.Part154.csC) (piBar (rhoBar 12467 BstLean.Part154.csC)) ≤ 1.65982E-7 := by
  have hr0 : 0 ≤ rhoBar 12467 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12467 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12467 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12467 BstLean.Part154.csC) (piBar (rhoBar 12467 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12467 BstLean.Part154.csC) (piBar (rhoBar 12467 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12467 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196047975 : ℝ) ^ 2 + 0.000124746592 ^ 2 + 3 * 0.000072416309 ^ 2 +
        2 * 0.797885 * 0.000196047975 * 0.000124746592 + 2 * 0.000196047975 * 0.000072416309 +
        4 * 0.797885 * 0.000124746592 * 0.000072416309 := by gcongr
    _ ≤ (1.65982E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12467 BstLean.Part154.csC Θ ≤ 0.002680179076 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12467 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12467 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12467 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12467 BstLean.Part154.csC) (piBar (rhoBar 12467 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12467 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036145254146 * 1.65982E-7 / (0.000256671598 : ℝ) := by gcongr
    _ ≤ 0.002680179076 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12467 BstLean.Part154.csC Θ ≤ 0.002974757995 + 0.000677234904 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12467 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12467 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12467 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036145254146 : ℝ) * ((2 * Θ * 0.000256671995 +
        (6863 / 10000) * 0.000256671995 * 12467 * 0.001026753861) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002974757995 + 0.000677234904 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12467 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12467 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12467 0.011 Θ ∧ gammaRatio 12467 0.011 Θ ≤ 0.000088237195 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12467 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036145254146 : ℝ) * 0.525 / ((1 - 0.011) * 12467) := by gcongr
      _ ≤ (0.000088237195 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12467 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12467 0.011 Θ) :=
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
    badAllowance 12467 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12467 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12467 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12467 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12467 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12467 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12467 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12467 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12467 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12467 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12467 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036145254146 : ℝ) * 12467 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12467 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003791132741 + 0.003357413980 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12467

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12467
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12467 BstLean.Part154.csC) (piBar (rhoBar 12467 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12467 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12467 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12467 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12467 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12467 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12467 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12467 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12467 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12467 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12467 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12467 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12467 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12467 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12467 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052977833786 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12467) ≤ 0.010695713323 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12467 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036145254146)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010695713323 + 2 * 0.737676 / 12467) := by gcongr
    _ ≤ (0.052977833786 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12467 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12467

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12467
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492834410 : ℝ) ≤ plow 12467 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12467) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053060375081)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407094015) : eMP 12467 0.011 xi bn ≤ 0.001211052263 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12467 : ℝ) * (1 - 0.011))) ≤ 0.000598766360 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001407094015 / (12467 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598766360 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598766360 : ℝ) + 3.141593 * 0.053060375081 / (12467 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001211052263 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053060375081)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407094015) : PiBarMP 12467 12 0.011 xi bn ≤ 0.162766489455 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12467 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037511251846 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.039916246366 : ℝ) ≤ √((12467 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.655720856568 : ℝ) ≤ √(12467 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12467) ≤ 0.124780066403 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037511251846 + 0.053060375081 * 1.772454 / (2 * (111.039916246366 : ℝ))) * (1 + 0.001211052263) +
        8 / (12467 * 111.655720856568) + 0.124780066403 := by gcongr
    _ ≤ (0.162766489455 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053060375081)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407094015) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283326211426) :
    parallelOracle 12467 0.011 xi bn cd ≤ 0.163776278911 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12467 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12467 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492834410 : ℝ) ≤ plow 12467 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.655720856568 : ℝ) ≤ √(12467 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283326211426 : ℝ) / (2 * 0.560492834410 * 111.655720856568)) * 0.162766489455 +
        0.283326211426 ^ 2 / (2 * 0.560492834410 * 111.655720856568) := by gcongr
    _ ≤ (0.163776278911 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053060375081) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407094015)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283326211426) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12467 12467 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492834410 : ℝ) ≤ plow 12467 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.655720856568 : ℝ) ≤ √(12467 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12467 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12467 Θ 1.22 ≤ 0.011876691045 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.655720856568 := by gcongr <;> linarith
      _ ≤ (0.011876691045 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12467 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12467 12467 0.011 ≤ 0.008561022135 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12467 12467 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12467 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12467 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12467 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12467 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163776278911 + 0.011876691045 + (0.008561022135 : ℝ) *
        (1 + 2 * (0.283326211426 + 0.011876691045) / (0.560492834410 * 111.655720856568))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12467]

end BstLean.Part269.N12467

/-! The original eight local profiles supply actual 12467 moment certificates. -/
namespace BstLean.Part269.N12467
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12467 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12467 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12467 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053060375081 ∧
    0 ≤ bN 12467 BstLean.Part154.csC (groupTheta g) ∧ bN 12467 BstLean.Part154.csC (groupTheta g) ≤ 0.001407094015 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12467 12467 0.011
      (momentAllowance 12467 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12467 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12467 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12467 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12467 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12467 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230348377640 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12467 0.011
      (momentAllowance 12467 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12467 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12467
/-! The actual computed-centre upper energy formula at 12467. -/
namespace BstLean.Part269.N12467
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12467

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12467
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12467)
open BstLean.Part268 (cell12467)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086201675991
  | 2 => 0.087158248642
  | 3 => 0.088115096365
  | 4 => 0.089074119956
  | 5 => 0.090037600988
  | 6 => 0.091008256043
  | 7 => 0.091989295619
  | 8 => 0.092984487687
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12467 12467 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12467 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003795409572 + 0.003362150420 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S4.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12467

/-! Actual upper energy certificates on all 43 source endpoints at 12467. -/
namespace BstLean.Part269.N12467
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12467)
open BstLean.Part268 (cell12467)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12467 (gMinus 12467) (1 - (cell12467 i).lower) ≤ 1 ∧
    energyUpper 12467 (gMinus 12467) (BstLean.Part211.gPlus 12467)
      (finiteEnergy 12467 12467 0.011) (1 - (cell12467 i).lower) ≤
      (cell12467 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨10,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨11,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨12,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨13,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨14,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨15,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨16,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨17,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨18,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨19,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨20,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨21,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨22,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨23,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨24,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨25,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨26,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨27,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨28,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨29,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨30,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨31,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨32,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨33,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨34,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨35,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨36,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨37,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨38,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨39,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨40,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨41,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨42,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨43,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨44,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨45,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨46,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨47,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨48,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨49,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨50,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨51,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12467) (by norm_num)
        (q := 1 - (cell12467 ⟨52,by decide⟩).lower)
        (by norm_num [cell12467]) (by norm_num [cell12467])
      exact ⟨E.1,E.2.trans (by norm_num [cell12467])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12467

/-! Source-cell containment and simple scalar guards at 12467. -/
namespace BstLean.Part269.N12467
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12467)
open BstLean.Part268 (cell12467)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12467 ⟨10,by decide⟩).lower ∧ (cell12467 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12467 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12467 ⟨11,by decide⟩).lower ∧ (cell12467 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12467 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12467 ⟨12,by decide⟩).lower ∧ (cell12467 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12467 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12467 ⟨13,by decide⟩).lower ∧ (cell12467 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12467 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12467 ⟨14,by decide⟩).lower ∧ (cell12467 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12467 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12467 ⟨15,by decide⟩).lower ∧ (cell12467 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12467 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12467 ⟨16,by decide⟩).lower ∧ (cell12467 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12467 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12467 ⟨17,by decide⟩).lower ∧ (cell12467 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12467 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12467 ⟨18,by decide⟩).lower ∧ (cell12467 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12467 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12467 ⟨19,by decide⟩).lower ∧ (cell12467 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12467 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12467 ⟨20,by decide⟩).lower ∧ (cell12467 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12467 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12467 ⟨21,by decide⟩).lower ∧ (cell12467 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12467 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12467 ⟨22,by decide⟩).lower ∧ (cell12467 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12467 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12467 ⟨23,by decide⟩).lower ∧ (cell12467 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12467 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12467 ⟨24,by decide⟩).lower ∧ (cell12467 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12467 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12467 ⟨25,by decide⟩).lower ∧ (cell12467 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12467 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12467 ⟨26,by decide⟩).lower ∧ (cell12467 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12467 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12467 ⟨27,by decide⟩).lower ∧ (cell12467 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12467 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12467 ⟨28,by decide⟩).lower ∧ (cell12467 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12467 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12467 ⟨29,by decide⟩).lower ∧ (cell12467 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12467 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12467 ⟨30,by decide⟩).lower ∧ (cell12467 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12467 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12467 ⟨31,by decide⟩).lower ∧ (cell12467 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12467 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12467 ⟨32,by decide⟩).lower ∧ (cell12467 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12467 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12467 ⟨33,by decide⟩).lower ∧ (cell12467 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12467 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12467 ⟨34,by decide⟩).lower ∧ (cell12467 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12467 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12467 ⟨35,by decide⟩).lower ∧ (cell12467 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12467 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12467 ⟨36,by decide⟩).lower ∧ (cell12467 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12467 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12467 ⟨37,by decide⟩).lower ∧ (cell12467 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12467 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12467 ⟨38,by decide⟩).lower ∧ (cell12467 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12467 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12467 ⟨39,by decide⟩).lower ∧ (cell12467 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12467 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12467 ⟨40,by decide⟩).lower ∧ (cell12467 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12467 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12467 ⟨41,by decide⟩).lower ∧ (cell12467 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12467 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12467 ⟨42,by decide⟩).lower ∧ (cell12467 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12467 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12467 ⟨43,by decide⟩).lower ∧ (cell12467 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12467 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12467 ⟨44,by decide⟩).lower ∧ (cell12467 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12467 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12467 ⟨45,by decide⟩).lower ∧ (cell12467 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12467 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12467 ⟨46,by decide⟩).lower ∧ (cell12467 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12467 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12467 ⟨47,by decide⟩).lower ∧ (cell12467 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12467 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12467 ⟨48,by decide⟩).lower ∧ (cell12467 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12467 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12467 ⟨49,by decide⟩).lower ∧ (cell12467 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12467 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12467 ⟨50,by decide⟩).lower ∧ (cell12467 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12467 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12467 ⟨51,by decide⟩).lower ∧ (cell12467 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12467 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12467 ⟨52,by decide⟩).lower ∧ (cell12467 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12467 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12467 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12467 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12467,cell12467,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12467 i).lower ∧
    (cell12467 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12467 i).upper ≤ (0.532 : ℝ) ∧
    (cell12467 i).centre ≤ (0.1 : ℝ) ∧ (cell12467 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12467 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12467 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12467

/-! The local source numeric instances at 12467 have no network premises. -/
namespace BstLean.Part269.N12467
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12467)
open BstLean.Part268 (cell12467)

noncomputable def sourceNumerics12467 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12467 (cell12467 i)
      scalarRow12467.M scalarRow12467.H scalarRow12467.xi := by
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
    energy_allowance := scalarRow12467.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12467]
    centre_nonneg := (scalarRow12467.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12467])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12467
/-! Actual 12468 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12468
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12468 ≤ (1.036143791729 : ℝ) := by
  have hr : (111.660198817662 : ℝ) ≤ √(12468 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.660198817662 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12468 12468 (11 / 1000) ≤
    (0.008560678806 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12468) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.660198817662 : ℝ) ≤ √(12468 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12468)
  have hdiv : K / √(12468 : ℝ) ≤ K / 111.660198817662 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.660198817662 ≤ (0.008560678806 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12468.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12468 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12468 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12468 := gPlus_lower 12468
end BstLean.Part269.N12468

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12468
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036143791728 : ℝ) ≤ wn 12468 := by
  have hn : √(12468 : ℝ) ≤ 111.660198817663 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12468 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.660198817663 ≤ 2 / √(12468 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256650649 : ℝ) ≤ rhoBar 12468 BstLean.Part154.csC ∧
    rhoBar 12468 BstLean.Part154.csC ≤ 0.000256651046 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036143791728 : ℝ) / (1.295212 * 12468) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036143791729 : ℝ) / (1.29521 * 12468) := by gcongr
      _ ≤ (0.000256651046 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12468 BstLean.Part154.csC) ≤ 0.001026670054 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12468 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12468 BstLean.Part154.csC) (piBar (rhoBar 12468 BstLean.Part154.csC)) ≤ 0.000196031973 ∧
    cc1 (rhoBar 12468 BstLean.Part154.csC) (piBar (rhoBar 12468 BstLean.Part154.csC)) ≤ 0.000124736411 ∧
    cc2 (rhoBar 12468 BstLean.Part154.csC) ≤ 0.000072410399 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12468 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12468 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12468 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12468 BstLean.Part154.csC * nuR (rhoBar 12468 BstLean.Part154.csC)) ≤ 0.000513318560 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256651046 : ℝ) * 0.001026670054 := by gcongr
      _ ≤ (0.000513318560 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12468 BstLean.Part154.csC) * nuR (rhoBar 12468 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001026670054 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12468 BstLean.Part154.csC) * rhoBar 12468 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256651046 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256651046 / 2 + 0.399 * 0.001026670054 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196031973 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513318560 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124736411 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256651046 / 1.414213562 := by gcongr
      _ ≤ (0.000072410399 : ℝ) := by norm_num

end BstLean.Part269.N12468

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12468
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12468 BstLean.Part154.csC) (piBar (rhoBar 12468 BstLean.Part154.csC)) ≤ 1.65954E-7 := by
  have hr0 : 0 ≤ rhoBar 12468 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12468 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12468 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12468 BstLean.Part154.csC) (piBar (rhoBar 12468 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12468 BstLean.Part154.csC) (piBar (rhoBar 12468 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12468 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196031973 : ℝ) ^ 2 + 0.000124736411 ^ 2 + 3 * 0.000072410399 ^ 2 +
        2 * 0.797885 * 0.000196031973 * 0.000124736411 + 2 * 0.000196031973 * 0.000072410399 +
        4 * 0.797885 * 0.000124736411 * 0.000072410399 := by gcongr
    _ ≤ (1.65954E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12468 BstLean.Part154.csC Θ ≤ 0.002679941898 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12468 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12468 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12468 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12468 BstLean.Part154.csC) (piBar (rhoBar 12468 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12468 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036143791729 * 1.65954E-7 / (0.000256650649 : ℝ) := by gcongr
    _ ≤ 0.002679941898 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12468 BstLean.Part154.csC Θ ≤ 0.002974506786 + 0.000677178674 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12468 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12468 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12468 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036143791729 : ℝ) * ((2 * Θ * 0.000256651046 +
        (6863 / 10000) * 0.000256651046 * 12468 * 0.001026670054) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002974506786 + 0.000677178674 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12468 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12468 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12468 0.011 Θ ∧ gammaRatio 12468 0.011 Θ ≤ 0.000088229993 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12468 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036143791729 : ℝ) * 0.525 / ((1 - 0.011) * 12468) := by gcongr
      _ ≤ (0.000088229993 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12468 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12468 0.011 Θ) :=
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
    badAllowance 12468 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12468 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12468 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12468 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12468 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12468 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12468 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12468 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12468 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12468 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12468 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036143791729 : ℝ) * 12468 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12468 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003790881532 + 0.003357120572 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12468

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12468
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12468 BstLean.Part154.csC) (piBar (rhoBar 12468 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12468 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12468 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12468 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12468 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12468 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12468 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12468 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12468 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12468 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12468 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12468 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12468 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12468 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12468 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052975685938 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12468) ≤ 0.010695284387 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12468 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036143791729)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010695284387 + 2 * 0.737676 / 12468) := by gcongr
    _ ≤ (0.052975685938 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12468 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12468

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12468
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492881336 : ℝ) ≤ plow 12468 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12468) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053059969833)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406969497) : eMP 12468 0.011 xi bn ≤ 0.001210950065 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12468 : ℝ) * (1 - 0.011))) ≤ 0.000598715855 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001406969497 / (12468 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598715855 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598715855 : ℝ) + 3.141593 * 0.053059969833 / (12468 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001210950065 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053059969833)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406969497) : PiBarMP 12468 12 0.011 xi bn ≤ 0.162759798743 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12468 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037509592067 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.044369510569 : ℝ) ≤ √((12468 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.660198817662 : ℝ) ≤ √(12468 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12468) ≤ 0.124775062290 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037509592067 + 0.053059969833 * 1.772454 / (2 * (111.044369510569 : ℝ))) * (1 + 0.001210950065) +
        8 / (12468 * 111.660198817662) + 0.124775062290 := by gcongr
    _ ≤ (0.162759798743 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053059969833)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406969497) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283323183934) :
    parallelOracle 12468 0.011 xi bn cd ≤ 0.163769514832 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12468 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12468 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492881336 : ℝ) ≤ plow 12468 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.660198817662 : ℝ) ≤ √(12468 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283323183934 : ℝ) / (2 * 0.560492881336 * 111.660198817662)) * 0.162759798743 +
        0.283323183934 ^ 2 / (2 * 0.560492881336 * 111.660198817662) := by gcongr
    _ ≤ (0.163769514832 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053059969833) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406969497)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283323183934) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12468 12468 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492881336 : ℝ) ≤ plow 12468 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.660198817662 : ℝ) ≤ √(12468 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12468 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12468 Θ 1.22 ≤ 0.011876214749 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.660198817662 := by gcongr <;> linarith
      _ ≤ (0.011876214749 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12468 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12468 12468 0.011 ≤ 0.008560678806 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12468 12468 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12468 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12468 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12468 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12468 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163769514832 + 0.011876214749 + (0.008560678806 : ℝ) *
        (1 + 2 * (0.283323183934 + 0.011876214749) / (0.560492881336 * 111.660198817662))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12468]

end BstLean.Part269.N12468

/-! The original eight local profiles supply actual 12468 moment certificates. -/
namespace BstLean.Part269.N12468
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12468 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12468 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12468 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053059969833 ∧
    0 ≤ bN 12468 BstLean.Part154.csC (groupTheta g) ∧ bN 12468 BstLean.Part154.csC (groupTheta g) ≤ 0.001406969497 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12468 12468 0.011
      (momentAllowance 12468 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12468 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12468 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12468 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12468 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12468 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230347497996 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12468 0.011
      (momentAllowance 12468 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12468 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12468
/-! The actual computed-centre upper energy formula at 12468. -/
namespace BstLean.Part269.N12468
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12468

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12468
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12468)
open BstLean.Part268 (cell12468)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086198474791
  | 2 => 0.087154981783
  | 3 => 0.088111753199
  | 4 => 0.089070687468
  | 5 => 0.090034063395
  | 6 => 0.091004594342
  | 7 => 0.091985487087
  | 8 => 0.092980505332
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12468 12468 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12468 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003795409572 + 0.003362150420 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S4.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12468

/-! Actual upper energy certificates on all 43 source endpoints at 12468. -/
namespace BstLean.Part269.N12468
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12468)
open BstLean.Part268 (cell12468)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12468 (gMinus 12468) (1 - (cell12468 i).lower) ≤ 1 ∧
    energyUpper 12468 (gMinus 12468) (BstLean.Part211.gPlus 12468)
      (finiteEnergy 12468 12468 0.011) (1 - (cell12468 i).lower) ≤
      (cell12468 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨10,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨11,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨12,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨13,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨14,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨15,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨16,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨17,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨18,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨19,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨20,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨21,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨22,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨23,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨24,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨25,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨26,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨27,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨28,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨29,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨30,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨31,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨32,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨33,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨34,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨35,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨36,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨37,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨38,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨39,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨40,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨41,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨42,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨43,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨44,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨45,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨46,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨47,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨48,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨49,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨50,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨51,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12468) (by norm_num)
        (q := 1 - (cell12468 ⟨52,by decide⟩).lower)
        (by norm_num [cell12468]) (by norm_num [cell12468])
      exact ⟨E.1,E.2.trans (by norm_num [cell12468])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12468

/-! Source-cell containment and simple scalar guards at 12468. -/
namespace BstLean.Part269.N12468
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12468)
open BstLean.Part268 (cell12468)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12468 ⟨10,by decide⟩).lower ∧ (cell12468 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12468 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12468 ⟨11,by decide⟩).lower ∧ (cell12468 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12468 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12468 ⟨12,by decide⟩).lower ∧ (cell12468 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12468 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12468 ⟨13,by decide⟩).lower ∧ (cell12468 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12468 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12468 ⟨14,by decide⟩).lower ∧ (cell12468 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12468 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12468 ⟨15,by decide⟩).lower ∧ (cell12468 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12468 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12468 ⟨16,by decide⟩).lower ∧ (cell12468 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12468 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12468 ⟨17,by decide⟩).lower ∧ (cell12468 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12468 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12468 ⟨18,by decide⟩).lower ∧ (cell12468 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12468 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12468 ⟨19,by decide⟩).lower ∧ (cell12468 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12468 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12468 ⟨20,by decide⟩).lower ∧ (cell12468 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12468 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12468 ⟨21,by decide⟩).lower ∧ (cell12468 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12468 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12468 ⟨22,by decide⟩).lower ∧ (cell12468 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12468 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12468 ⟨23,by decide⟩).lower ∧ (cell12468 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12468 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12468 ⟨24,by decide⟩).lower ∧ (cell12468 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12468 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12468 ⟨25,by decide⟩).lower ∧ (cell12468 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12468 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12468 ⟨26,by decide⟩).lower ∧ (cell12468 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12468 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12468 ⟨27,by decide⟩).lower ∧ (cell12468 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12468 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12468 ⟨28,by decide⟩).lower ∧ (cell12468 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12468 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12468 ⟨29,by decide⟩).lower ∧ (cell12468 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12468 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12468 ⟨30,by decide⟩).lower ∧ (cell12468 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12468 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12468 ⟨31,by decide⟩).lower ∧ (cell12468 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12468 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12468 ⟨32,by decide⟩).lower ∧ (cell12468 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12468 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12468 ⟨33,by decide⟩).lower ∧ (cell12468 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12468 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12468 ⟨34,by decide⟩).lower ∧ (cell12468 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12468 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12468 ⟨35,by decide⟩).lower ∧ (cell12468 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12468 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12468 ⟨36,by decide⟩).lower ∧ (cell12468 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12468 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12468 ⟨37,by decide⟩).lower ∧ (cell12468 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12468 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12468 ⟨38,by decide⟩).lower ∧ (cell12468 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12468 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12468 ⟨39,by decide⟩).lower ∧ (cell12468 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12468 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12468 ⟨40,by decide⟩).lower ∧ (cell12468 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12468 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12468 ⟨41,by decide⟩).lower ∧ (cell12468 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12468 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12468 ⟨42,by decide⟩).lower ∧ (cell12468 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12468 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12468 ⟨43,by decide⟩).lower ∧ (cell12468 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12468 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12468 ⟨44,by decide⟩).lower ∧ (cell12468 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12468 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12468 ⟨45,by decide⟩).lower ∧ (cell12468 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12468 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12468 ⟨46,by decide⟩).lower ∧ (cell12468 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12468 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12468 ⟨47,by decide⟩).lower ∧ (cell12468 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12468 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12468 ⟨48,by decide⟩).lower ∧ (cell12468 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12468 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12468 ⟨49,by decide⟩).lower ∧ (cell12468 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12468 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12468 ⟨50,by decide⟩).lower ∧ (cell12468 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12468 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12468 ⟨51,by decide⟩).lower ∧ (cell12468 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12468 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12468 ⟨52,by decide⟩).lower ∧ (cell12468 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12468 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12468 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12468 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12468,cell12468,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12468 i).lower ∧
    (cell12468 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12468 i).upper ≤ (0.532 : ℝ) ∧
    (cell12468 i).centre ≤ (0.1 : ℝ) ∧ (cell12468 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12468 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12468 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12468

/-! The local source numeric instances at 12468 have no network premises. -/
namespace BstLean.Part269.N12468
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12468)
open BstLean.Part268 (cell12468)

noncomputable def sourceNumerics12468 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12468 (cell12468 i)
      scalarRow12468.M scalarRow12468.H scalarRow12468.xi := by
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
    energy_allowance := scalarRow12468.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12468]
    centre_nonneg := (scalarRow12468.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12468])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12468
/-! Actual 12469 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12469
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12469 ≤ (1.036142329489 : ℝ) := by
  have hr : (111.664676599182 : ℝ) ≤ √(12469 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.664676599182 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12469 12469 (11 / 1000) ≤
    (0.008560335518 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12469) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.664676599182 : ℝ) ≤ √(12469 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12469)
  have hdiv : K / √(12469 : ℝ) ≤ K / 111.664676599182 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.664676599182 ≤ (0.008560335518 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12469.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12469 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12469 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12469 := gPlus_lower 12469
end BstLean.Part269.N12469

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12469
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036142329488 : ℝ) ≤ wn 12469 := by
  have hn : √(12469 : ℝ) ≤ 111.664676599183 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12469 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.664676599183 ≤ 2 / √(12469 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256629704 : ℝ) ≤ rhoBar 12469 BstLean.Part154.csC ∧
    rhoBar 12469 BstLean.Part154.csC ≤ 0.000256630101 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036142329488 : ℝ) / (1.295212 * 12469) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036142329489 : ℝ) / (1.29521 * 12469) := by gcongr
      _ ≤ (0.000256630101 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12469 BstLean.Part154.csC) ≤ 0.001026586264 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12469 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12469 BstLean.Part154.csC) (piBar (rhoBar 12469 BstLean.Part154.csC)) ≤ 0.000196015974 ∧
    cc1 (rhoBar 12469 BstLean.Part154.csC) (piBar (rhoBar 12469 BstLean.Part154.csC)) ≤ 0.000124726231 ∧
    cc2 (rhoBar 12469 BstLean.Part154.csC) ≤ 0.000072404490 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12469 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12469 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12469 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12469 BstLean.Part154.csC * nuR (rhoBar 12469 BstLean.Part154.csC)) ≤ 0.000513276667 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256630101 : ℝ) * 0.001026586264 := by gcongr
      _ ≤ (0.000513276667 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12469 BstLean.Part154.csC) * nuR (rhoBar 12469 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001026586264 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12469 BstLean.Part154.csC) * rhoBar 12469 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256630101 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256630101 / 2 + 0.399 * 0.001026586264 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196015974 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513276667 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124726231 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256630101 / 1.414213562 := by gcongr
      _ ≤ (0.000072404490 : ℝ) := by norm_num

end BstLean.Part269.N12469

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12469
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12469 BstLean.Part154.csC) (piBar (rhoBar 12469 BstLean.Part154.csC)) ≤ 1.65927E-7 := by
  have hr0 : 0 ≤ rhoBar 12469 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12469 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12469 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12469 BstLean.Part154.csC) (piBar (rhoBar 12469 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12469 BstLean.Part154.csC) (piBar (rhoBar 12469 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12469 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196015974 : ℝ) ^ 2 + 0.000124726231 ^ 2 + 3 * 0.000072404490 ^ 2 +
        2 * 0.797885 * 0.000196015974 * 0.000124726231 + 2 * 0.000196015974 * 0.000072404490 +
        4 * 0.797885 * 0.000124726231 * 0.000072404490 := by gcongr
    _ ≤ (1.65927E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12469 BstLean.Part154.csC Θ ≤ 0.002679720791 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12469 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12469 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12469 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12469 BstLean.Part154.csC) (piBar (rhoBar 12469 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12469 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036142329489 * 1.65927E-7 / (0.000256629704 : ℝ) := by gcongr
    _ ≤ 0.002679720791 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12469 BstLean.Part154.csC Θ ≤ 0.002974255635 + 0.000677122455 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12469 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12469 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12469 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036142329489 : ℝ) * ((2 * Θ * 0.000256630101 +
        (6863 / 10000) * 0.000256630101 * 12469 * 0.001026586264) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002974255635 + 0.000677122455 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12469 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12469 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12469 0.011 Θ ∧ gammaRatio 12469 0.011 Θ ≤ 0.000088222793 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12469 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036142329489 : ℝ) * 0.525 / ((1 - 0.011) * 12469) := by gcongr
      _ ≤ (0.000088222793 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12469 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12469 0.011 Θ) :=
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
    badAllowance 12469 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12469 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12469 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12469 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12469 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12469 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12469 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12469 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12469 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12469 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12469 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036142329489 : ℝ) * 12469 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12469 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003790630381 + 0.003356843246 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12469

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12469
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12469 BstLean.Part154.csC) (piBar (rhoBar 12469 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12469 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12469 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12469 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12469 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12469 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12469 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12469 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12469 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12469 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12469 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12469 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12469 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12469 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12469 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052973538358 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12469) ≤ 0.010694855504 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12469 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036142329489)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010694855504 + 2 * 0.737676 / 12469) := by gcongr
    _ ≤ (0.052973538358 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12469 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12469

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12469
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492928254 : ℝ) ≤ plow 12469 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12469) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053059573086)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406853416) : eMP 12469 0.011 xi bn ≤ 0.001210851466 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12469 : ℝ) * (1 - 0.011))) ≤ 0.000598667148 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001406853416 / (12469 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598667148 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598667148 : ℝ) + 3.141593 * 0.053059573086 / (12469 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001210851466 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053059573086)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406853416) : PiBarMP 12469 12 0.011 xi bn ≤ 0.162753221373 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12469 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037508044684 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.048822596189 : ℝ) ≤ √((12469 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.664676599182 : ℝ) ≤ √(12469 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12469) ≤ 0.124770058779 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037508044684 + 0.053059573086 * 1.772454 / (2 * (111.048822596189 : ℝ))) * (1 + 0.001210851466) +
        8 / (12469 * 111.664676599182) + 0.124770058779 := by gcongr
    _ ≤ (0.162753221373 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053059573086)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406853416) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283320175161) :
    parallelOracle 12469 0.011 xi bn cd ≤ 0.163762864468 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12469 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12469 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492928254 : ℝ) ≤ plow 12469 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.664676599182 : ℝ) ≤ √(12469 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283320175161 : ℝ) / (2 * 0.560492928254 * 111.664676599182)) * 0.162753221373 +
        0.283320175161 ^ 2 / (2 * 0.560492928254 * 111.664676599182) := by gcongr
    _ ≤ (0.163762864468 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053059573086) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406853416)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283320175161) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12469 12469 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492928254 : ℝ) ≤ plow 12469 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.664676599182 : ℝ) ≤ √(12469 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12469 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12469 Θ 1.22 ≤ 0.011875738510 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.664676599182 := by gcongr <;> linarith
      _ ≤ (0.011875738510 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12469 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12469 12469 0.011 ≤ 0.008560335518 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12469 12469 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12469 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12469 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12469 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12469 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163762864468 + 0.011875738510 + (0.008560335518 : ℝ) *
        (1 + 2 * (0.283320175161 + 0.011875738510) / (0.560492928254 * 111.664676599182))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12469]

end BstLean.Part269.N12469

/-! The original eight local profiles supply actual 12469 moment certificates. -/
namespace BstLean.Part269.N12469
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12469 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12469 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12469 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053059573086 ∧
    0 ≤ bN 12469 BstLean.Part154.csC (groupTheta g) ∧ bN 12469 BstLean.Part154.csC (groupTheta g) ≤ 0.001406853416 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12469 12469 0.011
      (momentAllowance 12469 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12469 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12469 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12469 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12469 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12469 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230346636803 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12469 0.011
      (momentAllowance 12469 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12469 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12469
/-! The actual computed-centre upper energy formula at 12469. -/
namespace BstLean.Part269.N12469
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12469

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12469
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12469)
open BstLean.Part268 (cell12469)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086195274973
  | 2 => 0.087151716365
  | 3 => 0.088108411548
  | 4 => 0.089067256586
  | 5 => 0.090030527519
  | 6 => 0.091000934493
  | 7 => 0.091981680570
  | 8 => 0.092976525186
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12469 12469 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12469 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003795409572 + 0.003362150420 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S4.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12469

/-! Actual upper energy certificates on all 43 source endpoints at 12469. -/
namespace BstLean.Part269.N12469
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12469)
open BstLean.Part268 (cell12469)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12469 (gMinus 12469) (1 - (cell12469 i).lower) ≤ 1 ∧
    energyUpper 12469 (gMinus 12469) (BstLean.Part211.gPlus 12469)
      (finiteEnergy 12469 12469 0.011) (1 - (cell12469 i).lower) ≤
      (cell12469 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨10,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨11,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨12,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨13,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨14,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨15,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨16,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨17,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨18,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨19,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨20,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨21,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨22,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨23,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨24,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨25,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨26,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨27,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨28,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨29,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨30,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨31,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨32,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨33,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨34,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨35,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨36,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨37,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨38,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨39,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨40,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨41,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨42,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨43,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨44,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨45,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨46,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨47,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨48,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨49,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨50,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨51,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12469) (by norm_num)
        (q := 1 - (cell12469 ⟨52,by decide⟩).lower)
        (by norm_num [cell12469]) (by norm_num [cell12469])
      exact ⟨E.1,E.2.trans (by norm_num [cell12469])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12469

/-! Source-cell containment and simple scalar guards at 12469. -/
namespace BstLean.Part269.N12469
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12469)
open BstLean.Part268 (cell12469)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12469 ⟨10,by decide⟩).lower ∧ (cell12469 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12469 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12469 ⟨11,by decide⟩).lower ∧ (cell12469 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12469 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12469 ⟨12,by decide⟩).lower ∧ (cell12469 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12469 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12469 ⟨13,by decide⟩).lower ∧ (cell12469 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12469 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12469 ⟨14,by decide⟩).lower ∧ (cell12469 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12469 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12469 ⟨15,by decide⟩).lower ∧ (cell12469 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12469 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12469 ⟨16,by decide⟩).lower ∧ (cell12469 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12469 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12469 ⟨17,by decide⟩).lower ∧ (cell12469 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12469 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12469 ⟨18,by decide⟩).lower ∧ (cell12469 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12469 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12469 ⟨19,by decide⟩).lower ∧ (cell12469 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12469 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12469 ⟨20,by decide⟩).lower ∧ (cell12469 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12469 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12469 ⟨21,by decide⟩).lower ∧ (cell12469 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12469 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12469 ⟨22,by decide⟩).lower ∧ (cell12469 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12469 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12469 ⟨23,by decide⟩).lower ∧ (cell12469 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12469 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12469 ⟨24,by decide⟩).lower ∧ (cell12469 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12469 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12469 ⟨25,by decide⟩).lower ∧ (cell12469 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12469 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12469 ⟨26,by decide⟩).lower ∧ (cell12469 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12469 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12469 ⟨27,by decide⟩).lower ∧ (cell12469 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12469 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12469 ⟨28,by decide⟩).lower ∧ (cell12469 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12469 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12469 ⟨29,by decide⟩).lower ∧ (cell12469 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12469 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12469 ⟨30,by decide⟩).lower ∧ (cell12469 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12469 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12469 ⟨31,by decide⟩).lower ∧ (cell12469 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12469 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12469 ⟨32,by decide⟩).lower ∧ (cell12469 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12469 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12469 ⟨33,by decide⟩).lower ∧ (cell12469 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12469 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12469 ⟨34,by decide⟩).lower ∧ (cell12469 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12469 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12469 ⟨35,by decide⟩).lower ∧ (cell12469 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12469 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12469 ⟨36,by decide⟩).lower ∧ (cell12469 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12469 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12469 ⟨37,by decide⟩).lower ∧ (cell12469 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12469 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12469 ⟨38,by decide⟩).lower ∧ (cell12469 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12469 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12469 ⟨39,by decide⟩).lower ∧ (cell12469 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12469 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12469 ⟨40,by decide⟩).lower ∧ (cell12469 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12469 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12469 ⟨41,by decide⟩).lower ∧ (cell12469 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12469 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12469 ⟨42,by decide⟩).lower ∧ (cell12469 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12469 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12469 ⟨43,by decide⟩).lower ∧ (cell12469 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12469 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12469 ⟨44,by decide⟩).lower ∧ (cell12469 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12469 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12469 ⟨45,by decide⟩).lower ∧ (cell12469 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12469 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12469 ⟨46,by decide⟩).lower ∧ (cell12469 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12469 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12469 ⟨47,by decide⟩).lower ∧ (cell12469 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12469 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12469 ⟨48,by decide⟩).lower ∧ (cell12469 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12469 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12469 ⟨49,by decide⟩).lower ∧ (cell12469 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12469 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12469 ⟨50,by decide⟩).lower ∧ (cell12469 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12469 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12469 ⟨51,by decide⟩).lower ∧ (cell12469 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12469 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12469 ⟨52,by decide⟩).lower ∧ (cell12469 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12469 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12469 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12469 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12469,cell12469,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12469 i).lower ∧
    (cell12469 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12469 i).upper ≤ (0.532 : ℝ) ∧
    (cell12469 i).centre ≤ (0.1 : ℝ) ∧ (cell12469 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12469 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12469 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12469

/-! The local source numeric instances at 12469 have no network premises. -/
namespace BstLean.Part269.N12469
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12469)
open BstLean.Part268 (cell12469)

noncomputable def sourceNumerics12469 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12469 (cell12469 i)
      scalarRow12469.M scalarRow12469.H scalarRow12469.xi := by
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
    energy_allowance := scalarRow12469.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12469]
    centre_nonneg := (scalarRow12469.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12469])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12469
/-! Actual 12470 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12470
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12470 ≤ (1.036140867427 : ℝ) := by
  have hr : (111.669154201149 : ℝ) ≤ √(12470 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.669154201149 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12470 12470 (11 / 1000) ≤
    (0.008559992271 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12470) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.669154201149 : ℝ) ≤ √(12470 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12470)
  have hdiv : K / √(12470 : ℝ) ≤ K / 111.669154201149 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.669154201149 ≤ (0.008559992271 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12470.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12470 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12470 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12470 := gPlus_lower 12470
end BstLean.Part269.N12470

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12470
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036140867426 : ℝ) ≤ wn 12470 := by
  have hn : √(12470 : ℝ) ≤ 111.669154201150 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12470 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.669154201150 ≤ 2 / √(12470 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256608762 : ℝ) ≤ rhoBar 12470 BstLean.Part154.csC ∧
    rhoBar 12470 BstLean.Part154.csC ≤ 0.000256609159 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036140867426 : ℝ) / (1.295212 * 12470) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036140867427 : ℝ) / (1.29521 * 12470) := by gcongr
      _ ≤ (0.000256609159 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12470 BstLean.Part154.csC) ≤ 0.001026502485 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12470 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12470 BstLean.Part154.csC) (piBar (rhoBar 12470 BstLean.Part154.csC)) ≤ 0.000195999978 ∧
    cc1 (rhoBar 12470 BstLean.Part154.csC) (piBar (rhoBar 12470 BstLean.Part154.csC)) ≤ 0.000124716052 ∧
    cc2 (rhoBar 12470 BstLean.Part154.csC) ≤ 0.000072398581 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12470 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12470 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12470 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12470 BstLean.Part154.csC * nuR (rhoBar 12470 BstLean.Part154.csC)) ≤ 0.000513234780 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256609159 : ℝ) * 0.001026502485 := by gcongr
      _ ≤ (0.000513234780 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12470 BstLean.Part154.csC) * nuR (rhoBar 12470 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001026502485 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12470 BstLean.Part154.csC) * rhoBar 12470 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256609159 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256609159 / 2 + 0.399 * 0.001026502485 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195999978 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513234780 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124716052 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256609159 / 1.414213562 := by gcongr
      _ ≤ (0.000072398581 : ℝ) := by norm_num

end BstLean.Part269.N12470

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12470
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12470 BstLean.Part154.csC) (piBar (rhoBar 12470 BstLean.Part154.csC)) ≤ 1.65900E-7 := by
  have hr0 : 0 ≤ rhoBar 12470 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12470 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12470 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12470 BstLean.Part154.csC) (piBar (rhoBar 12470 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12470 BstLean.Part154.csC) (piBar (rhoBar 12470 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12470 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195999978 : ℝ) ^ 2 + 0.000124716052 ^ 2 + 3 * 0.000072398581 ^ 2 +
        2 * 0.797885 * 0.000195999978 * 0.000124716052 + 2 * 0.000195999978 * 0.000072398581 +
        4 * 0.797885 * 0.000124716052 * 0.000072398581 := by gcongr
    _ ≤ (1.65900E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12470 BstLean.Part154.csC Θ ≤ 0.002679499618 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12470 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12470 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12470 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12470 BstLean.Part154.csC) (piBar (rhoBar 12470 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12470 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036140867427 * 1.65900E-7 / (0.000256608762 : ℝ) := by gcongr
    _ ≤ 0.002679499618 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12470 BstLean.Part154.csC Θ ≤ 0.002974004514 + 0.000677066244 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12470 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12470 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12470 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036140867427 : ℝ) * ((2 * Θ * 0.000256609159 +
        (6863 / 10000) * 0.000256609159 * 12470 * 0.001026502485) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002974004514 + 0.000677066244 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12470 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12470 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12470 0.011 Θ ∧ gammaRatio 12470 0.011 Θ ≤ 0.000088215593 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12470 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036140867427 : ℝ) * 0.525 / ((1 - 0.011) * 12470) := by gcongr
      _ ≤ (0.000088215593 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12470 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12470 0.011 Θ) :=
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
    badAllowance 12470 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12470 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12470 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12470 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12470 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12470 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12470 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12470 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12470 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12470 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12470 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036140867427 : ℝ) * 12470 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12470 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003790379260 + 0.003356565862 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12470

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12470
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12470 BstLean.Part154.csC) (piBar (rhoBar 12470 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12470 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12470 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12470 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12470 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12470 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12470 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12470 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12470 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12470 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12470 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12470 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12470 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12470 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12470 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052971391034 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12470) ≤ 0.010694426672 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12470 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036140867427)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010694426672 + 2 * 0.737676 / 12470) := by gcongr
    _ ≤ (0.052971391034 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12470 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12470

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12470
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492975164 : ℝ) ≤ plow 12470 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12470) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053059176338)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406737300) : eMP 12470 0.011 xi bn ≤ 0.001210752861 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12470 : ℝ) * (1 - 0.011))) ≤ 0.000598618438 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001406737300 / (12470 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598618438 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598618438 : ℝ) + 3.141593 * 0.053059176338 / (12470 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001210752861 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053059176338)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406737300) : PiBarMP 12470 12 0.011 xi bn ≤ 0.162746644076 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12470 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037506496771 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.053275503246 : ℝ) ≤ √((12470 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.669154201149 : ℝ) ≤ √(12470 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12470) ≤ 0.124765055870 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037506496771 + 0.053059176338 * 1.772454 / (2 * (111.053275503246 : ℝ))) * (1 + 0.001210752861) +
        8 / (12470 * 111.669154201149) + 0.124765055870 := by gcongr
    _ ≤ (0.162746644076 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053059176338)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406737300) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283317166637) :
    parallelOracle 12470 0.011 xi bn cd ≤ 0.163756214186 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12470 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12470 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492975164 : ℝ) ≤ plow 12470 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.669154201149 : ℝ) ≤ √(12470 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283317166637 : ℝ) / (2 * 0.560492975164 * 111.669154201149)) * 0.162746644076 +
        0.283317166637 ^ 2 / (2 * 0.560492975164 * 111.669154201149) := by gcongr
    _ ≤ (0.163756214186 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053059176338) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406737300)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283317166637) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12470 12470 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492975164 : ℝ) ≤ plow 12470 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.669154201149 : ℝ) ≤ √(12470 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12470 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12470 Θ 1.22 ≤ 0.011875262328 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.669154201149 := by gcongr <;> linarith
      _ ≤ (0.011875262328 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12470 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12470 12470 0.011 ≤ 0.008559992271 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12470 12470 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12470 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12470 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12470 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12470 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163756214186 + 0.011875262328 + (0.008559992271 : ℝ) *
        (1 + 2 * (0.283317166637 + 0.011875262328) / (0.560492975164 * 111.669154201149))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12470]

end BstLean.Part269.N12470

/-! The original eight local profiles supply actual 12470 moment certificates. -/
namespace BstLean.Part269.N12470
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12470 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12470 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12470 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053059176338 ∧
    0 ≤ bN 12470 BstLean.Part154.csC (groupTheta g) ∧ bN 12470 BstLean.Part154.csC (groupTheta g) ≤ 0.001406737300 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12470 12470 0.011
      (momentAllowance 12470 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12470 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12470 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12470 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12470 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12470 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230345775603 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12470 0.011
      (momentAllowance 12470 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12470 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12470
/-! The actual computed-centre upper energy formula at 12470. -/
namespace BstLean.Part269.N12470
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12470

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12470
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12470)
open BstLean.Part268 (cell12470)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086192076535
  | 2 => 0.087148452386
  | 3 => 0.088105071410
  | 4 => 0.089063827310
  | 5 => 0.090026993360
  | 6 => 0.090997276494
  | 7 => 0.091977876065
  | 8 => 0.092972547249
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12470 12470 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12470 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003795409572 + 0.003362150420 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S4.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12470

/-! Actual upper energy certificates on all 43 source endpoints at 12470. -/
namespace BstLean.Part269.N12470
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12470)
open BstLean.Part268 (cell12470)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12470 (gMinus 12470) (1 - (cell12470 i).lower) ≤ 1 ∧
    energyUpper 12470 (gMinus 12470) (BstLean.Part211.gPlus 12470)
      (finiteEnergy 12470 12470 0.011) (1 - (cell12470 i).lower) ≤
      (cell12470 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨10,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨11,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨12,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨13,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨14,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨15,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨16,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨17,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨18,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨19,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨20,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨21,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨22,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨23,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨24,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨25,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨26,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨27,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨28,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨29,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨30,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨31,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨32,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨33,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨34,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨35,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨36,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨37,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨38,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨39,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨40,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨41,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨42,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨43,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨44,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨45,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨46,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨47,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨48,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨49,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨50,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨51,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12470) (by norm_num)
        (q := 1 - (cell12470 ⟨52,by decide⟩).lower)
        (by norm_num [cell12470]) (by norm_num [cell12470])
      exact ⟨E.1,E.2.trans (by norm_num [cell12470])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12470

/-! Source-cell containment and simple scalar guards at 12470. -/
namespace BstLean.Part269.N12470
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12470)
open BstLean.Part268 (cell12470)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12470 ⟨10,by decide⟩).lower ∧ (cell12470 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12470 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12470 ⟨11,by decide⟩).lower ∧ (cell12470 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12470 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12470 ⟨12,by decide⟩).lower ∧ (cell12470 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12470 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12470 ⟨13,by decide⟩).lower ∧ (cell12470 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12470 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12470 ⟨14,by decide⟩).lower ∧ (cell12470 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12470 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12470 ⟨15,by decide⟩).lower ∧ (cell12470 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12470 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12470 ⟨16,by decide⟩).lower ∧ (cell12470 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12470 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12470 ⟨17,by decide⟩).lower ∧ (cell12470 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12470 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12470 ⟨18,by decide⟩).lower ∧ (cell12470 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12470 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12470 ⟨19,by decide⟩).lower ∧ (cell12470 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12470 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12470 ⟨20,by decide⟩).lower ∧ (cell12470 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12470 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12470 ⟨21,by decide⟩).lower ∧ (cell12470 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12470 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12470 ⟨22,by decide⟩).lower ∧ (cell12470 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12470 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12470 ⟨23,by decide⟩).lower ∧ (cell12470 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12470 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12470 ⟨24,by decide⟩).lower ∧ (cell12470 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12470 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12470 ⟨25,by decide⟩).lower ∧ (cell12470 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12470 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12470 ⟨26,by decide⟩).lower ∧ (cell12470 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12470 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12470 ⟨27,by decide⟩).lower ∧ (cell12470 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12470 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12470 ⟨28,by decide⟩).lower ∧ (cell12470 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12470 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12470 ⟨29,by decide⟩).lower ∧ (cell12470 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12470 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12470 ⟨30,by decide⟩).lower ∧ (cell12470 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12470 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12470 ⟨31,by decide⟩).lower ∧ (cell12470 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12470 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12470 ⟨32,by decide⟩).lower ∧ (cell12470 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12470 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12470 ⟨33,by decide⟩).lower ∧ (cell12470 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12470 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12470 ⟨34,by decide⟩).lower ∧ (cell12470 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12470 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12470 ⟨35,by decide⟩).lower ∧ (cell12470 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12470 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12470 ⟨36,by decide⟩).lower ∧ (cell12470 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12470 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12470 ⟨37,by decide⟩).lower ∧ (cell12470 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12470 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12470 ⟨38,by decide⟩).lower ∧ (cell12470 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12470 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12470 ⟨39,by decide⟩).lower ∧ (cell12470 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12470 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12470 ⟨40,by decide⟩).lower ∧ (cell12470 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12470 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12470 ⟨41,by decide⟩).lower ∧ (cell12470 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12470 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12470 ⟨42,by decide⟩).lower ∧ (cell12470 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12470 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12470 ⟨43,by decide⟩).lower ∧ (cell12470 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12470 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12470 ⟨44,by decide⟩).lower ∧ (cell12470 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12470 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12470 ⟨45,by decide⟩).lower ∧ (cell12470 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12470 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12470 ⟨46,by decide⟩).lower ∧ (cell12470 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12470 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12470 ⟨47,by decide⟩).lower ∧ (cell12470 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12470 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12470 ⟨48,by decide⟩).lower ∧ (cell12470 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12470 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12470 ⟨49,by decide⟩).lower ∧ (cell12470 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12470 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12470 ⟨50,by decide⟩).lower ∧ (cell12470 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12470 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12470 ⟨51,by decide⟩).lower ∧ (cell12470 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12470 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12470 ⟨52,by decide⟩).lower ∧ (cell12470 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12470 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12470 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12470 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12470,cell12470,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12470 i).lower ∧
    (cell12470 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12470 i).upper ≤ (0.532 : ℝ) ∧
    (cell12470 i).centre ≤ (0.1 : ℝ) ∧ (cell12470 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12470 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12470 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12470

/-! The local source numeric instances at 12470 have no network premises. -/
namespace BstLean.Part269.N12470
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12470)
open BstLean.Part268 (cell12470)

noncomputable def sourceNumerics12470 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12470 (cell12470 i)
      scalarRow12470.M scalarRow12470.H scalarRow12470.xi := by
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
    energy_allowance := scalarRow12470.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12470]
    centre_nonneg := (scalarRow12470.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12470])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12470
/-! Actual 12471 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12471
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12471 ≤ (1.036139405541 : ℝ) := by
  have hr : (111.673631623584 : ℝ) ≤ √(12471 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.673631623584 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12471 12471 (11 / 1000) ≤
    (0.008559649066 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12471) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.673631623584 : ℝ) ≤ √(12471 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12471)
  have hdiv : K / √(12471 : ℝ) ≤ K / 111.673631623584 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.673631623584 ≤ (0.008559649066 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12471.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12471 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12471 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12471 := gPlus_lower 12471
end BstLean.Part269.N12471

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12471
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036139405540 : ℝ) ≤ wn 12471 := by
  have hn : √(12471 : ℝ) ≤ 111.673631623585 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12471 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.673631623585 ≤ 2 / √(12471 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256587823 : ℝ) ≤ rhoBar 12471 BstLean.Part154.csC ∧
    rhoBar 12471 BstLean.Part154.csC ≤ 0.000256588221 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036139405540 : ℝ) / (1.295212 * 12471) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036139405541 : ℝ) / (1.29521 * 12471) := by gcongr
      _ ≤ (0.000256588221 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12471 BstLean.Part154.csC) ≤ 0.001026418722 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12471 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12471 BstLean.Part154.csC) (piBar (rhoBar 12471 BstLean.Part154.csC)) ≤ 0.000195983985 ∧
    cc1 (rhoBar 12471 BstLean.Part154.csC) (piBar (rhoBar 12471 BstLean.Part154.csC)) ≤ 0.000124705876 ∧
    cc2 (rhoBar 12471 BstLean.Part154.csC) ≤ 0.000072392674 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12471 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12471 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12471 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12471 BstLean.Part154.csC * nuR (rhoBar 12471 BstLean.Part154.csC)) ≤ 0.000513192902 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256588221 : ℝ) * 0.001026418722 := by gcongr
      _ ≤ (0.000513192902 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12471 BstLean.Part154.csC) * nuR (rhoBar 12471 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001026418722 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12471 BstLean.Part154.csC) * rhoBar 12471 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256588221 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256588221 / 2 + 0.399 * 0.001026418722 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195983985 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513192902 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124705876 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256588221 / 1.414213562 := by gcongr
      _ ≤ (0.000072392674 : ℝ) := by norm_num

end BstLean.Part269.N12471

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12471
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12471 BstLean.Part154.csC) (piBar (rhoBar 12471 BstLean.Part154.csC)) ≤ 1.65873E-7 := by
  have hr0 : 0 ≤ rhoBar 12471 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12471 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12471 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12471 BstLean.Part154.csC) (piBar (rhoBar 12471 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12471 BstLean.Part154.csC) (piBar (rhoBar 12471 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12471 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195983985 : ℝ) ^ 2 + 0.000124705876 ^ 2 + 3 * 0.000072392674 ^ 2 +
        2 * 0.797885 * 0.000195983985 * 0.000124705876 + 2 * 0.000195983985 * 0.000072392674 +
        4 * 0.797885 * 0.000124705876 * 0.000072392674 := by gcongr
    _ ≤ (1.65873E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12471 BstLean.Part154.csC Θ ≤ 0.002679278379 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12471 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12471 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12471 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12471 BstLean.Part154.csC) (piBar (rhoBar 12471 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12471 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036139405541 * 1.65873E-7 / (0.000256587823 : ℝ) := by gcongr
    _ ≤ 0.002679278379 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12471 BstLean.Part154.csC Θ ≤ 0.002973753448 + 0.000677010043 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12471 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12471 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12471 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036139405541 : ℝ) * ((2 * Θ * 0.000256588221 +
        (6863 / 10000) * 0.000256588221 * 12471 * 0.001026418722) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002973753448 + 0.000677010043 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12471 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12471 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12471 0.011 Θ ∧ gammaRatio 12471 0.011 Θ ≤ 0.000088208395 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12471 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036139405541 : ℝ) * 0.525 / ((1 - 0.011) * 12471) := by gcongr
      _ ≤ (0.000088208395 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12471 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12471 0.011 Θ) :=
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
    badAllowance 12471 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12471 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12471 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12471 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12471 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12471 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12471 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12471 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12471 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12471 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12471 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036139405541 : ℝ) * 12471 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12471 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003790128194 + 0.003356288422 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12471

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12471
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12471 BstLean.Part154.csC) (piBar (rhoBar 12471 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12471 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12471 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12471 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12471 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12471 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12471 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12471 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12471 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12471 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12471 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12471 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12471 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12471 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12471 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052969243968 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12471) ≤ 0.010693997891 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12471 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036139405541)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010693997891 + 2 * 0.737676 / 12471) := by gcongr
    _ ≤ (0.052969243968 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12471 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12471

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12471
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493022067 : ℝ) ≤ plow 12471 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12471) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053058779616)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406621149) : eMP 12471 0.011 xi bn ≤ 0.001210654250 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12471 : ℝ) * (1 - 0.011))) ≤ 0.000598569725 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001406621149 / (12471 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598569725 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598569725 : ℝ) + 3.141593 * 0.053058779616 / (12471 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001210654250 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053058779616)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406621149) : PiBarMP 12471 12 0.011 xi bn ≤ 0.162740066851 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12471 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037504948327 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.057728231762 : ℝ) ≤ √((12471 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.673631623584 : ℝ) ≤ √(12471 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12471) ≤ 0.124760053562 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037504948327 + 0.053058779616 * 1.772454 / (2 * (111.057728231762 : ℝ))) * (1 + 0.001210654250) +
        8 / (12471 * 111.673631623584) + 0.124760053562 := by gcongr
    _ ≤ (0.162740066851 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053058779616)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406621149) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283314158425) :
    parallelOracle 12471 0.011 xi bn cd ≤ 0.163749563987 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12471 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12471 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493022067 : ℝ) ≤ plow 12471 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.673631623584 : ℝ) ≤ √(12471 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283314158425 : ℝ) / (2 * 0.560493022067 * 111.673631623584)) * 0.162740066851 +
        0.283314158425 ^ 2 / (2 * 0.560493022067 * 111.673631623584) := by gcongr
    _ ≤ (0.163749563987 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053058779616) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406621149)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283314158425) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12471 12471 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493022067 : ℝ) ≤ plow 12471 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.673631623584 : ℝ) ≤ √(12471 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12471 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12471 Θ 1.22 ≤ 0.011874786203 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.673631623584 := by gcongr <;> linarith
      _ ≤ (0.011874786203 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12471 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12471 12471 0.011 ≤ 0.008559649066 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12471 12471 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12471 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12471 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12471 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12471 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163749563987 + 0.011874786203 + (0.008559649066 : ℝ) *
        (1 + 2 * (0.283314158425 + 0.011874786203) / (0.560493022067 * 111.673631623584))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12471]

end BstLean.Part269.N12471

/-! The original eight local profiles supply actual 12471 moment certificates. -/
namespace BstLean.Part269.N12471
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12471 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12471 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12471 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053058779616 ∧
    0 ≤ bN 12471 BstLean.Part154.csC (groupTheta g) ∧ bN 12471 BstLean.Part154.csC (groupTheta g) ≤ 0.001406621149 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12471 12471 0.011
      (momentAllowance 12471 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12471 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12471 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12471 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12471 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12471 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230344914457 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12471 0.011
      (momentAllowance 12471 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12471 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12471
/-! The actual computed-centre upper energy formula at 12471. -/
namespace BstLean.Part269.N12471
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12471

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12471
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12471)
open BstLean.Part268 (cell12471)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086188879475
  | 2 => 0.087145189846
  | 3 => 0.088101732785
  | 4 => 0.089060399636
  | 5 => 0.090023460914
  | 6 => 0.090993620344
  | 7 => 0.091974073571
  | 8 => 0.092968571516
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12471 12471 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12471 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003795409572 + 0.003362150420 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S4.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12471

/-! Actual upper energy certificates on all 43 source endpoints at 12471. -/
namespace BstLean.Part269.N12471
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12471)
open BstLean.Part268 (cell12471)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12471 (gMinus 12471) (1 - (cell12471 i).lower) ≤ 1 ∧
    energyUpper 12471 (gMinus 12471) (BstLean.Part211.gPlus 12471)
      (finiteEnergy 12471 12471 0.011) (1 - (cell12471 i).lower) ≤
      (cell12471 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨10,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨11,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨12,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨13,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨14,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨15,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨16,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨17,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨18,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨19,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨20,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨21,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨22,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨23,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨24,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨25,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨26,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨27,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨28,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨29,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨30,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨31,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨32,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨33,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨34,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨35,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨36,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨37,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨38,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨39,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨40,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨41,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨42,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨43,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨44,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨45,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨46,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨47,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨48,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨49,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨50,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨51,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12471) (by norm_num)
        (q := 1 - (cell12471 ⟨52,by decide⟩).lower)
        (by norm_num [cell12471]) (by norm_num [cell12471])
      exact ⟨E.1,E.2.trans (by norm_num [cell12471])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12471

/-! Source-cell containment and simple scalar guards at 12471. -/
namespace BstLean.Part269.N12471
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12471)
open BstLean.Part268 (cell12471)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12471 ⟨10,by decide⟩).lower ∧ (cell12471 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12471 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12471 ⟨11,by decide⟩).lower ∧ (cell12471 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12471 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12471 ⟨12,by decide⟩).lower ∧ (cell12471 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12471 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12471 ⟨13,by decide⟩).lower ∧ (cell12471 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12471 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12471 ⟨14,by decide⟩).lower ∧ (cell12471 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12471 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12471 ⟨15,by decide⟩).lower ∧ (cell12471 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12471 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12471 ⟨16,by decide⟩).lower ∧ (cell12471 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12471 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12471 ⟨17,by decide⟩).lower ∧ (cell12471 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12471 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12471 ⟨18,by decide⟩).lower ∧ (cell12471 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12471 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12471 ⟨19,by decide⟩).lower ∧ (cell12471 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12471 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12471 ⟨20,by decide⟩).lower ∧ (cell12471 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12471 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12471 ⟨21,by decide⟩).lower ∧ (cell12471 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12471 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12471 ⟨22,by decide⟩).lower ∧ (cell12471 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12471 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12471 ⟨23,by decide⟩).lower ∧ (cell12471 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12471 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12471 ⟨24,by decide⟩).lower ∧ (cell12471 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12471 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12471 ⟨25,by decide⟩).lower ∧ (cell12471 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12471 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12471 ⟨26,by decide⟩).lower ∧ (cell12471 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12471 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12471 ⟨27,by decide⟩).lower ∧ (cell12471 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12471 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12471 ⟨28,by decide⟩).lower ∧ (cell12471 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12471 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12471 ⟨29,by decide⟩).lower ∧ (cell12471 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12471 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12471 ⟨30,by decide⟩).lower ∧ (cell12471 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12471 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12471 ⟨31,by decide⟩).lower ∧ (cell12471 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12471 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12471 ⟨32,by decide⟩).lower ∧ (cell12471 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12471 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12471 ⟨33,by decide⟩).lower ∧ (cell12471 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12471 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12471 ⟨34,by decide⟩).lower ∧ (cell12471 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12471 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12471 ⟨35,by decide⟩).lower ∧ (cell12471 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12471 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12471 ⟨36,by decide⟩).lower ∧ (cell12471 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12471 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12471 ⟨37,by decide⟩).lower ∧ (cell12471 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12471 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12471 ⟨38,by decide⟩).lower ∧ (cell12471 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12471 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12471 ⟨39,by decide⟩).lower ∧ (cell12471 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12471 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12471 ⟨40,by decide⟩).lower ∧ (cell12471 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12471 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12471 ⟨41,by decide⟩).lower ∧ (cell12471 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12471 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12471 ⟨42,by decide⟩).lower ∧ (cell12471 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12471 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12471 ⟨43,by decide⟩).lower ∧ (cell12471 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12471 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12471 ⟨44,by decide⟩).lower ∧ (cell12471 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12471 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12471 ⟨45,by decide⟩).lower ∧ (cell12471 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12471 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12471 ⟨46,by decide⟩).lower ∧ (cell12471 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12471 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12471 ⟨47,by decide⟩).lower ∧ (cell12471 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12471 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12471 ⟨48,by decide⟩).lower ∧ (cell12471 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12471 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12471 ⟨49,by decide⟩).lower ∧ (cell12471 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12471 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12471 ⟨50,by decide⟩).lower ∧ (cell12471 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12471 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12471 ⟨51,by decide⟩).lower ∧ (cell12471 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12471 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12471 ⟨52,by decide⟩).lower ∧ (cell12471 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12471 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12471 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12471 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12471,cell12471,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12471 i).lower ∧
    (cell12471 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12471 i).upper ≤ (0.532 : ℝ) ∧
    (cell12471 i).centre ≤ (0.1 : ℝ) ∧ (cell12471 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12471 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12471 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12471

/-! The local source numeric instances at 12471 have no network premises. -/
namespace BstLean.Part269.N12471
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12471)
open BstLean.Part268 (cell12471)

noncomputable def sourceNumerics12471 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12471 (cell12471 i)
      scalarRow12471.M scalarRow12471.H scalarRow12471.xi := by
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
    energy_allowance := scalarRow12471.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12471]
    centre_nonneg := (scalarRow12471.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12471])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12471
/-! Actual 12472 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12472
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12472 ≤ (1.036137943832 : ℝ) := by
  have hr : (111.678108866509 : ℝ) ≤ √(12472 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.678108866509 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12472 12472 (11 / 1000) ≤
    (0.008559305902 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12472) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.678108866509 : ℝ) ≤ √(12472 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12472)
  have hdiv : K / √(12472 : ℝ) ≤ K / 111.678108866509 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.678108866509 ≤ (0.008559305902 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12472.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12472 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12472 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12472 := gPlus_lower 12472
end BstLean.Part269.N12472

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12472
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036137943831 : ℝ) ≤ wn 12472 := by
  have hn : √(12472 : ℝ) ≤ 111.678108866510 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12472 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.678108866510 ≤ 2 / √(12472 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256566888 : ℝ) ≤ rhoBar 12472 BstLean.Part154.csC ∧
    rhoBar 12472 BstLean.Part154.csC ≤ 0.000256567285 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036137943831 : ℝ) / (1.295212 * 12472) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036137943832 : ℝ) / (1.29521 * 12472) := by gcongr
      _ ≤ (0.000256567285 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12472 BstLean.Part154.csC) ≤ 0.001026334967 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12472 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12472 BstLean.Part154.csC) (piBar (rhoBar 12472 BstLean.Part154.csC)) ≤ 0.000195967993 ∧
    cc1 (rhoBar 12472 BstLean.Part154.csC) (piBar (rhoBar 12472 BstLean.Part154.csC)) ≤ 0.000124695700 ∧
    cc2 (rhoBar 12472 BstLean.Part154.csC) ≤ 0.000072386767 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12472 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12472 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12472 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12472 BstLean.Part154.csC * nuR (rhoBar 12472 BstLean.Part154.csC)) ≤ 0.000513151027 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256567285 : ℝ) * 0.001026334967 := by gcongr
      _ ≤ (0.000513151027 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12472 BstLean.Part154.csC) * nuR (rhoBar 12472 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001026334967 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12472 BstLean.Part154.csC) * rhoBar 12472 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256567285 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256567285 / 2 + 0.399 * 0.001026334967 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195967993 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513151027 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124695700 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256567285 / 1.414213562 := by gcongr
      _ ≤ (0.000072386767 : ℝ) := by norm_num

end BstLean.Part269.N12472

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12472
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12472 BstLean.Part154.csC) (piBar (rhoBar 12472 BstLean.Part154.csC)) ≤ 1.65846E-7 := by
  have hr0 : 0 ≤ rhoBar 12472 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12472 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12472 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12472 BstLean.Part154.csC) (piBar (rhoBar 12472 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12472 BstLean.Part154.csC) (piBar (rhoBar 12472 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12472 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195967993 : ℝ) ^ 2 + 0.000124695700 ^ 2 + 3 * 0.000072386767 ^ 2 +
        2 * 0.797885 * 0.000195967993 * 0.000124695700 + 2 * 0.000195967993 * 0.000072386767 +
        4 * 0.797885 * 0.000124695700 * 0.000072386767 := by gcongr
    _ ≤ (1.65846E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12472 BstLean.Part154.csC Θ ≤ 0.002679057065 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12472 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12472 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12472 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12472 BstLean.Part154.csC) (piBar (rhoBar 12472 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12472 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036137943832 * 1.65846E-7 / (0.000256566888 : ℝ) := by gcongr
    _ ≤ 0.002679057065 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12472 BstLean.Part154.csC Θ ≤ 0.002973502392 + 0.000676953848 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12472 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12472 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12472 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036137943832 : ℝ) * ((2 * Θ * 0.000256567285 +
        (6863 / 10000) * 0.000256567285 * 12472 * 0.001026334967) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002973502392 + 0.000676953848 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12472 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12472 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12472 0.011 Θ ∧ gammaRatio 12472 0.011 Θ ≤ 0.000088201198 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12472 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036137943832 : ℝ) * 0.525 / ((1 - 0.011) * 12472) := by gcongr
      _ ≤ (0.000088201198 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12472 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12472 0.011 Θ) :=
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
    badAllowance 12472 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12472 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12472 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12472 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12472 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12472 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12472 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12472 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12472 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12472 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12472 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036137943832 : ℝ) * 12472 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12472 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003789877138 + 0.003356010913 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12472

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12472
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12472 BstLean.Part154.csC) (piBar (rhoBar 12472 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12472 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12472 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12472 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12472 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12472 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12472 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12472 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12472 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12472 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12472 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12472 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12472 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12472 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12472 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052967097169 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12472) ≤ 0.010693569163 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12472 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036137943832)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010693569163 + 2 * 0.737676 / 12472) := by gcongr
    _ ≤ (0.052967097169 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12472 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12472

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12472
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493068962 : ℝ) ≤ plow 12472 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12472) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053058382868)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406504960) : eMP 12472 0.011 xi bn ≤ 0.001210555629 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12472 : ℝ) * (1 - 0.011))) ≤ 0.000598521007 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001406504960 / (12472 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598521007 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598521007 : ℝ) + 3.141593 * 0.053058382868 / (12472 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001210555629 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053058382868)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406504960) : PiBarMP 12472 12 0.011 xi bn ≤ 0.162733489660 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12472 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037503399313 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.062180781758 : ℝ) ≤ √((12472 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.678108866509 : ℝ) ≤ √(12472 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12472) ≤ 0.124755051856 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037503399313 + 0.053058382868 * 1.772454 / (2 * (111.062180781758 : ℝ))) * (1 + 0.001210555629) +
        8 / (12472 * 111.678108866509) + 0.124755051856 := by gcongr
    _ ≤ (0.162733489660 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053058382868)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406504960) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283311150420) :
    parallelOracle 12472 0.011 xi bn cd ≤ 0.163742913830 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12472 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12472 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493068962 : ℝ) ≤ plow 12472 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.678108866509 : ℝ) ≤ √(12472 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283311150420 : ℝ) / (2 * 0.560493068962 * 111.678108866509)) * 0.162733489660 +
        0.283311150420 ^ 2 / (2 * 0.560493068962 * 111.678108866509) := by gcongr
    _ ≤ (0.163742913830 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053058382868) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406504960)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283311150420) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12472 12472 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493068962 : ℝ) ≤ plow 12472 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.678108866509 : ℝ) ≤ √(12472 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12472 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12472 Θ 1.22 ≤ 0.011874310136 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.678108866509 := by gcongr <;> linarith
      _ ≤ (0.011874310136 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12472 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12472 12472 0.011 ≤ 0.008559305902 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12472 12472 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12472 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12472 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12472 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12472 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163742913830 + 0.011874310136 + (0.008559305902 : ℝ) *
        (1 + 2 * (0.283311150420 + 0.011874310136) / (0.560493068962 * 111.678108866509))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12472]

end BstLean.Part269.N12472

/-! The original eight local profiles supply actual 12472 moment certificates. -/
namespace BstLean.Part269.N12472
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12472 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12472 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12472 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053058382868 ∧
    0 ≤ bN 12472 BstLean.Part154.csC (groupTheta g) ∧ bN 12472 BstLean.Part154.csC (groupTheta g) ≤ 0.001406504960 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12472 12472 0.011
      (momentAllowance 12472 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12472 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12472 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12472 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12472 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12472 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230344053251 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12472 0.011
      (momentAllowance 12472 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12472 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12472
/-! The actual computed-centre upper energy formula at 12472. -/
namespace BstLean.Part269.N12472
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12472

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12472
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12472)
open BstLean.Part268 (cell12472)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086185683791
  | 2 => 0.087141928743
  | 3 => 0.088098395671
  | 4 => 0.089056973564
  | 5 => 0.090019930180
  | 6 => 0.090989966040
  | 7 => 0.091970273086
  | 8 => 0.092964597985
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12472 12472 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12472 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003795409572 + 0.003362150420 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S4.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12472

/-! Actual upper energy certificates on all 43 source endpoints at 12472. -/
namespace BstLean.Part269.N12472
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12472)
open BstLean.Part268 (cell12472)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12472 (gMinus 12472) (1 - (cell12472 i).lower) ≤ 1 ∧
    energyUpper 12472 (gMinus 12472) (BstLean.Part211.gPlus 12472)
      (finiteEnergy 12472 12472 0.011) (1 - (cell12472 i).lower) ≤
      (cell12472 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨10,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨11,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨12,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨13,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨14,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨15,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨16,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨17,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨18,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨19,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨20,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨21,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨22,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨23,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨24,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨25,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨26,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨27,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨28,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨29,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨30,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨31,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨32,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨33,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨34,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨35,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨36,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨37,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨38,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨39,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨40,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨41,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨42,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨43,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨44,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨45,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨46,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨47,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨48,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨49,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨50,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨51,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12472) (by norm_num)
        (q := 1 - (cell12472 ⟨52,by decide⟩).lower)
        (by norm_num [cell12472]) (by norm_num [cell12472])
      exact ⟨E.1,E.2.trans (by norm_num [cell12472])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12472

/-! Source-cell containment and simple scalar guards at 12472. -/
namespace BstLean.Part269.N12472
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12472)
open BstLean.Part268 (cell12472)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12472 ⟨10,by decide⟩).lower ∧ (cell12472 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12472 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12472 ⟨11,by decide⟩).lower ∧ (cell12472 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12472 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12472 ⟨12,by decide⟩).lower ∧ (cell12472 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12472 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12472 ⟨13,by decide⟩).lower ∧ (cell12472 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12472 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12472 ⟨14,by decide⟩).lower ∧ (cell12472 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12472 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12472 ⟨15,by decide⟩).lower ∧ (cell12472 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12472 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12472 ⟨16,by decide⟩).lower ∧ (cell12472 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12472 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12472 ⟨17,by decide⟩).lower ∧ (cell12472 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12472 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12472 ⟨18,by decide⟩).lower ∧ (cell12472 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12472 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12472 ⟨19,by decide⟩).lower ∧ (cell12472 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12472 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12472 ⟨20,by decide⟩).lower ∧ (cell12472 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12472 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12472 ⟨21,by decide⟩).lower ∧ (cell12472 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12472 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12472 ⟨22,by decide⟩).lower ∧ (cell12472 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12472 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12472 ⟨23,by decide⟩).lower ∧ (cell12472 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12472 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12472 ⟨24,by decide⟩).lower ∧ (cell12472 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12472 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12472 ⟨25,by decide⟩).lower ∧ (cell12472 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12472 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12472 ⟨26,by decide⟩).lower ∧ (cell12472 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12472 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12472 ⟨27,by decide⟩).lower ∧ (cell12472 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12472 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12472 ⟨28,by decide⟩).lower ∧ (cell12472 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12472 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12472 ⟨29,by decide⟩).lower ∧ (cell12472 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12472 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12472 ⟨30,by decide⟩).lower ∧ (cell12472 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12472 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12472 ⟨31,by decide⟩).lower ∧ (cell12472 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12472 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12472 ⟨32,by decide⟩).lower ∧ (cell12472 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12472 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12472 ⟨33,by decide⟩).lower ∧ (cell12472 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12472 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12472 ⟨34,by decide⟩).lower ∧ (cell12472 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12472 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12472 ⟨35,by decide⟩).lower ∧ (cell12472 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12472 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12472 ⟨36,by decide⟩).lower ∧ (cell12472 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12472 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12472 ⟨37,by decide⟩).lower ∧ (cell12472 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12472 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12472 ⟨38,by decide⟩).lower ∧ (cell12472 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12472 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12472 ⟨39,by decide⟩).lower ∧ (cell12472 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12472 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12472 ⟨40,by decide⟩).lower ∧ (cell12472 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12472 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12472 ⟨41,by decide⟩).lower ∧ (cell12472 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12472 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12472 ⟨42,by decide⟩).lower ∧ (cell12472 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12472 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12472 ⟨43,by decide⟩).lower ∧ (cell12472 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12472 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12472 ⟨44,by decide⟩).lower ∧ (cell12472 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12472 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12472 ⟨45,by decide⟩).lower ∧ (cell12472 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12472 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12472 ⟨46,by decide⟩).lower ∧ (cell12472 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12472 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12472 ⟨47,by decide⟩).lower ∧ (cell12472 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12472 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12472 ⟨48,by decide⟩).lower ∧ (cell12472 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12472 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12472 ⟨49,by decide⟩).lower ∧ (cell12472 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12472 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12472 ⟨50,by decide⟩).lower ∧ (cell12472 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12472 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12472 ⟨51,by decide⟩).lower ∧ (cell12472 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12472 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12472 ⟨52,by decide⟩).lower ∧ (cell12472 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12472 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12472 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12472 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12472,cell12472,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12472 i).lower ∧
    (cell12472 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12472 i).upper ≤ (0.532 : ℝ) ∧
    (cell12472 i).centre ≤ (0.1 : ℝ) ∧ (cell12472 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12472 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12472 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12472

/-! The local source numeric instances at 12472 have no network premises. -/
namespace BstLean.Part269.N12472
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12472)
open BstLean.Part268 (cell12472)

noncomputable def sourceNumerics12472 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12472 (cell12472 i)
      scalarRow12472.M scalarRow12472.H scalarRow12472.xi := by
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
    energy_allowance := scalarRow12472.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12472]
    centre_nonneg := (scalarRow12472.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12472])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12472
/-! Actual 12473 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12473
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12473 ≤ (1.036136482300 : ℝ) := by
  have hr : (111.682585929947 : ℝ) ≤ √(12473 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.682585929947 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12473 12473 (11 / 1000) ≤
    (0.008558962779 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12473) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.682585929947 : ℝ) ≤ √(12473 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12473)
  have hdiv : K / √(12473 : ℝ) ≤ K / 111.682585929947 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.682585929947 ≤ (0.008558962779 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12473.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12473 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12473 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12473 := gPlus_lower 12473
end BstLean.Part269.N12473

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12473
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036136482299 : ℝ) ≤ wn 12473 := by
  have hn : √(12473 : ℝ) ≤ 111.682585929948 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12473 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.682585929948 ≤ 2 / √(12473 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256545957 : ℝ) ≤ rhoBar 12473 BstLean.Part154.csC ∧
    rhoBar 12473 BstLean.Part154.csC ≤ 0.000256546354 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036136482299 : ℝ) / (1.295212 * 12473) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036136482300 : ℝ) / (1.29521 * 12473) := by gcongr
      _ ≤ (0.000256546354 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12473 BstLean.Part154.csC) ≤ 0.001026251233 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12473 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12473 BstLean.Part154.csC) (piBar (rhoBar 12473 BstLean.Part154.csC)) ≤ 0.000195952005 ∧
    cc1 (rhoBar 12473 BstLean.Part154.csC) (piBar (rhoBar 12473 BstLean.Part154.csC)) ≤ 0.000124685527 ∧
    cc2 (rhoBar 12473 BstLean.Part154.csC) ≤ 0.000072380861 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12473 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12473 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12473 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12473 BstLean.Part154.csC * nuR (rhoBar 12473 BstLean.Part154.csC)) ≤ 0.000513109162 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256546354 : ℝ) * 0.001026251233 := by gcongr
      _ ≤ (0.000513109162 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12473 BstLean.Part154.csC) * nuR (rhoBar 12473 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001026251233 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12473 BstLean.Part154.csC) * rhoBar 12473 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256546354 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256546354 / 2 + 0.399 * 0.001026251233 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195952005 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513109162 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124685527 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256546354 / 1.414213562 := by gcongr
      _ ≤ (0.000072380861 : ℝ) := by norm_num

end BstLean.Part269.N12473

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12473
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12473 BstLean.Part154.csC) (piBar (rhoBar 12473 BstLean.Part154.csC)) ≤ 1.65819E-7 := by
  have hr0 : 0 ≤ rhoBar 12473 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12473 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12473 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12473 BstLean.Part154.csC) (piBar (rhoBar 12473 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12473 BstLean.Part154.csC) (piBar (rhoBar 12473 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12473 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195952005 : ℝ) ^ 2 + 0.000124685527 ^ 2 + 3 * 0.000072380861 ^ 2 +
        2 * 0.797885 * 0.000195952005 * 0.000124685527 + 2 * 0.000195952005 * 0.000072380861 +
        4 * 0.797885 * 0.000124685527 * 0.000072380861 := by gcongr
    _ ≤ (1.65819E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12473 BstLean.Part154.csC Θ ≤ 0.002678835674 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12473 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12473 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12473 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12473 BstLean.Part154.csC) (piBar (rhoBar 12473 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12473 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036136482300 * 1.65819E-7 / (0.000256545957 : ℝ) := by gcongr
    _ ≤ 0.002678835674 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12473 BstLean.Part154.csC Θ ≤ 0.002973251417 + 0.000676897667 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12473 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12473 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12473 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036136482300 : ℝ) * ((2 * Θ * 0.000256546354 +
        (6863 / 10000) * 0.000256546354 * 12473 * 0.001026251233) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002973251417 + 0.000676897667 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12473 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12473 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12473 0.011 Θ ∧ gammaRatio 12473 0.011 Θ ≤ 0.000088194003 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12473 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036136482300 : ℝ) * 0.525 / ((1 - 0.011) * 12473) := by gcongr
      _ ≤ (0.000088194003 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12473 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12473 0.011 Θ) :=
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
    badAllowance 12473 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12473 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12473 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12473 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12473 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12473 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12473 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12473 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12473 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12473 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12473 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036136482300 : ℝ) * 12473 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12473 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003789626163 + 0.003355733341 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12473

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12473
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12473 BstLean.Part154.csC) (piBar (rhoBar 12473 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12473 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12473 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12473 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12473 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12473 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12473 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12473 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12473 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12473 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12473 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12473 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12473 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12473 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12473 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052964950623 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12473) ≤ 0.010693140485 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12473 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036136482300)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010693140485 + 2 * 0.737676 / 12473) := by gcongr
    _ ≤ (0.052964950623 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12473 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12473

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12473
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493115850 : ℝ) ≤ plow 12473 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12473) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057986168)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406388729) : eMP 12473 0.011 xi bn ≤ 0.001210456999 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12473 : ℝ) * (1 - 0.011))) ≤ 0.000598472284 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001406388729 / (12473 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598472284 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598472284 : ℝ) + 3.141593 * 0.053057986168 / (12473 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001210456999 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057986168)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406388729) : PiBarMP 12473 12 0.011 xi bn ≤ 0.162726912448 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12473 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037501849675 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.066633153256 : ℝ) ≤ √((12473 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.682585929947 : ℝ) ≤ √(12473 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12473) ≤ 0.124750050751 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037501849675 + 0.053057986168 * 1.772454 / (2 * (111.066633153256 : ℝ))) * (1 + 0.001210456999) +
        8 / (12473 * 111.682585929947) + 0.124750050751 := by gcongr
    _ ≤ (0.162726912448 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057986168)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406388729) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283308142769) :
    parallelOracle 12473 0.011 xi bn cd ≤ 0.163736263663 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12473 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12473 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493115850 : ℝ) ≤ plow 12473 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.682585929947 : ℝ) ≤ √(12473 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283308142769 : ℝ) / (2 * 0.560493115850 * 111.682585929947)) * 0.162726912448 +
        0.283308142769 ^ 2 / (2 * 0.560493115850 * 111.682585929947) := by gcongr
    _ ≤ (0.163736263663 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057986168) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406388729)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283308142769) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12473 12473 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493115850 : ℝ) ≤ plow 12473 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.682585929947 : ℝ) ≤ √(12473 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12473 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12473 Θ 1.22 ≤ 0.011873834126 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.682585929947 := by gcongr <;> linarith
      _ ≤ (0.011873834126 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12473 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12473 12473 0.011 ≤ 0.008558962779 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12473 12473 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12473 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12473 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12473 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12473 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163736263663 + 0.011873834126 + (0.008558962779 : ℝ) *
        (1 + 2 * (0.283308142769 + 0.011873834126) / (0.560493115850 * 111.682585929947))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12473]

end BstLean.Part269.N12473

/-! The original eight local profiles supply actual 12473 moment certificates. -/
namespace BstLean.Part269.N12473
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12473 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12473 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12473 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053057986168 ∧
    0 ≤ bN 12473 BstLean.Part154.csC (groupTheta g) ∧ bN 12473 BstLean.Part154.csC (groupTheta g) ≤ 0.001406388729 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12473 12473 0.011
      (momentAllowance 12473 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12473 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12473 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12473 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12473 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12473 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230343192146 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12473 0.011
      (momentAllowance 12473 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12473 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12473
/-! The actual computed-centre upper energy formula at 12473. -/
namespace BstLean.Part269.N12473
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12473

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12473
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12473)
open BstLean.Part268 (cell12473)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086182489482
  | 2 => 0.087138669074
  | 3 => 0.088095060066
  | 4 => 0.089053549092
  | 5 => 0.090016401157
  | 6 => 0.090986313581
  | 7 => 0.091966474606
  | 8 => 0.092960626654
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12473 12473 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12473 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003795409572 + 0.003362150420 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S4.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12473

/-! Actual upper energy certificates on all 43 source endpoints at 12473. -/
namespace BstLean.Part269.N12473
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12473)
open BstLean.Part268 (cell12473)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12473 (gMinus 12473) (1 - (cell12473 i).lower) ≤ 1 ∧
    energyUpper 12473 (gMinus 12473) (BstLean.Part211.gPlus 12473)
      (finiteEnergy 12473 12473 0.011) (1 - (cell12473 i).lower) ≤
      (cell12473 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨10,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨11,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨12,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨13,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨14,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨15,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨16,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨17,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨18,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨19,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨20,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨21,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨22,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨23,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨24,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨25,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨26,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨27,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨28,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨29,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨30,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨31,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨32,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨33,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨34,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨35,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨36,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨37,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨38,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨39,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨40,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨41,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨42,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨43,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨44,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨45,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨46,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨47,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨48,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨49,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨50,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨51,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12473) (by norm_num)
        (q := 1 - (cell12473 ⟨52,by decide⟩).lower)
        (by norm_num [cell12473]) (by norm_num [cell12473])
      exact ⟨E.1,E.2.trans (by norm_num [cell12473])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12473

/-! Source-cell containment and simple scalar guards at 12473. -/
namespace BstLean.Part269.N12473
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12473)
open BstLean.Part268 (cell12473)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12473 ⟨10,by decide⟩).lower ∧ (cell12473 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12473 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12473 ⟨11,by decide⟩).lower ∧ (cell12473 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12473 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12473 ⟨12,by decide⟩).lower ∧ (cell12473 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12473 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12473 ⟨13,by decide⟩).lower ∧ (cell12473 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12473 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12473 ⟨14,by decide⟩).lower ∧ (cell12473 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12473 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12473 ⟨15,by decide⟩).lower ∧ (cell12473 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12473 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12473 ⟨16,by decide⟩).lower ∧ (cell12473 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12473 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12473 ⟨17,by decide⟩).lower ∧ (cell12473 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12473 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12473 ⟨18,by decide⟩).lower ∧ (cell12473 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12473 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12473 ⟨19,by decide⟩).lower ∧ (cell12473 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12473 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12473 ⟨20,by decide⟩).lower ∧ (cell12473 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12473 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12473 ⟨21,by decide⟩).lower ∧ (cell12473 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12473 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12473 ⟨22,by decide⟩).lower ∧ (cell12473 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12473 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12473 ⟨23,by decide⟩).lower ∧ (cell12473 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12473 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12473 ⟨24,by decide⟩).lower ∧ (cell12473 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12473 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12473 ⟨25,by decide⟩).lower ∧ (cell12473 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12473 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12473 ⟨26,by decide⟩).lower ∧ (cell12473 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12473 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12473 ⟨27,by decide⟩).lower ∧ (cell12473 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12473 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12473 ⟨28,by decide⟩).lower ∧ (cell12473 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12473 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12473 ⟨29,by decide⟩).lower ∧ (cell12473 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12473 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12473 ⟨30,by decide⟩).lower ∧ (cell12473 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12473 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12473 ⟨31,by decide⟩).lower ∧ (cell12473 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12473 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12473 ⟨32,by decide⟩).lower ∧ (cell12473 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12473 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12473 ⟨33,by decide⟩).lower ∧ (cell12473 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12473 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12473 ⟨34,by decide⟩).lower ∧ (cell12473 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12473 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12473 ⟨35,by decide⟩).lower ∧ (cell12473 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12473 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12473 ⟨36,by decide⟩).lower ∧ (cell12473 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12473 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12473 ⟨37,by decide⟩).lower ∧ (cell12473 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12473 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12473 ⟨38,by decide⟩).lower ∧ (cell12473 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12473 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12473 ⟨39,by decide⟩).lower ∧ (cell12473 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12473 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12473 ⟨40,by decide⟩).lower ∧ (cell12473 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12473 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12473 ⟨41,by decide⟩).lower ∧ (cell12473 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12473 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12473 ⟨42,by decide⟩).lower ∧ (cell12473 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12473 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12473 ⟨43,by decide⟩).lower ∧ (cell12473 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12473 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12473 ⟨44,by decide⟩).lower ∧ (cell12473 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12473 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12473 ⟨45,by decide⟩).lower ∧ (cell12473 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12473 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12473 ⟨46,by decide⟩).lower ∧ (cell12473 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12473 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12473 ⟨47,by decide⟩).lower ∧ (cell12473 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12473 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12473 ⟨48,by decide⟩).lower ∧ (cell12473 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12473 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12473 ⟨49,by decide⟩).lower ∧ (cell12473 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12473 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12473 ⟨50,by decide⟩).lower ∧ (cell12473 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12473 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12473 ⟨51,by decide⟩).lower ∧ (cell12473 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12473 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12473 ⟨52,by decide⟩).lower ∧ (cell12473 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12473 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12473 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12473 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12473,cell12473,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12473 i).lower ∧
    (cell12473 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12473 i).upper ≤ (0.532 : ℝ) ∧
    (cell12473 i).centre ≤ (0.1 : ℝ) ∧ (cell12473 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12473 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12473 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12473

/-! The local source numeric instances at 12473 have no network premises. -/
namespace BstLean.Part269.N12473
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12473)
open BstLean.Part268 (cell12473)

noncomputable def sourceNumerics12473 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12473 (cell12473 i)
      scalarRow12473.M scalarRow12473.H scalarRow12473.xi := by
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
    energy_allowance := scalarRow12473.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12473]
    centre_nonneg := (scalarRow12473.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12473])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12473
/-! Actual 12474 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12474
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12474 ≤ (1.036135020945 : ℝ) := by
  have hr : (111.687062813917 : ℝ) ≤ √(12474 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.687062813917 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12474 12474 (11 / 1000) ≤
    (0.008558619697 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12474) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.687062813917 : ℝ) ≤ √(12474 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12474)
  have hdiv : K / √(12474 : ℝ) ≤ K / 111.687062813917 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.687062813917 ≤ (0.008558619697 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12474.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12474 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12474 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12474 := gPlus_lower 12474
end BstLean.Part269.N12474

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12474
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036135020944 : ℝ) ≤ wn 12474 := by
  have hn : √(12474 : ℝ) ≤ 111.687062813918 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12474 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.687062813918 ≤ 2 / √(12474 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256525028 : ℝ) ≤ rhoBar 12474 BstLean.Part154.csC ∧
    rhoBar 12474 BstLean.Part154.csC ≤ 0.000256525425 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036135020944 : ℝ) / (1.295212 * 12474) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036135020945 : ℝ) / (1.29521 * 12474) := by gcongr
      _ ≤ (0.000256525425 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12474 BstLean.Part154.csC) ≤ 0.001026167506 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12474 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12474 BstLean.Part154.csC) (piBar (rhoBar 12474 BstLean.Part154.csC)) ≤ 0.000195936018 ∧
    cc1 (rhoBar 12474 BstLean.Part154.csC) (piBar (rhoBar 12474 BstLean.Part154.csC)) ≤ 0.000124675355 ∧
    cc2 (rhoBar 12474 BstLean.Part154.csC) ≤ 0.000072374957 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12474 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12474 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12474 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12474 BstLean.Part154.csC * nuR (rhoBar 12474 BstLean.Part154.csC)) ≤ 0.000513067302 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256525425 : ℝ) * 0.001026167506 := by gcongr
      _ ≤ (0.000513067302 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12474 BstLean.Part154.csC) * nuR (rhoBar 12474 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001026167506 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12474 BstLean.Part154.csC) * rhoBar 12474 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256525425 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256525425 / 2 + 0.399 * 0.001026167506 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195936018 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513067302 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124675355 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256525425 / 1.414213562 := by gcongr
      _ ≤ (0.000072374957 : ℝ) := by norm_num

end BstLean.Part269.N12474

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12474
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12474 BstLean.Part154.csC) (piBar (rhoBar 12474 BstLean.Part154.csC)) ≤ 1.65792E-7 := by
  have hr0 : 0 ≤ rhoBar 12474 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12474 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12474 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12474 BstLean.Part154.csC) (piBar (rhoBar 12474 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12474 BstLean.Part154.csC) (piBar (rhoBar 12474 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12474 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195936018 : ℝ) ^ 2 + 0.000124675355 ^ 2 + 3 * 0.000072374957 ^ 2 +
        2 * 0.797885 * 0.000195936018 * 0.000124675355 + 2 * 0.000195936018 * 0.000072374957 +
        4 * 0.797885 * 0.000124675355 * 0.000072374957 := by gcongr
    _ ≤ (1.65792E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12474 BstLean.Part154.csC Θ ≤ 0.002678614227 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12474 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12474 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12474 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12474 BstLean.Part154.csC) (piBar (rhoBar 12474 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12474 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036135020945 * 1.65792E-7 / (0.000256525028 : ℝ) := by gcongr
    _ ≤ 0.002678614227 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12474 BstLean.Part154.csC Θ ≤ 0.002973000449 + 0.000676841491 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12474 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12474 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12474 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036135020945 : ℝ) * ((2 * Θ * 0.000256525425 +
        (6863 / 10000) * 0.000256525425 * 12474 * 0.001026167506) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002973000449 + 0.000676841491 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12474 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12474 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12474 0.011 Θ ∧ gammaRatio 12474 0.011 Θ ≤ 0.000088186808 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12474 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036135020945 : ℝ) * 0.525 / ((1 - 0.011) * 12474) := by gcongr
      _ ≤ (0.000088186808 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12474 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12474 0.011 Θ) :=
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
    badAllowance 12474 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12474 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12474 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12474 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12474 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12474 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12474 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12474 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12474 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12474 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12474 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036135020945 : ℝ) * 12474 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12474 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003789375195 + 0.003355455718 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12474

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12474
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12474 BstLean.Part154.csC) (piBar (rhoBar 12474 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12474 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12474 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12474 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12474 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12474 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12474 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12474 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12474 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12474 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12474 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12474 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12474 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12474 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12474 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052962804343 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12474) ≤ 0.010692711860 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12474 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036135020945)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010692711860 + 2 * 0.737676 / 12474) := by gcongr
    _ ≤ (0.052962804343 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12474 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12474

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12474
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493162730 : ℝ) ≤ plow 12474 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12474) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057589447)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406272470) : eMP 12474 0.011 xi bn ≤ 0.001210358365 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12474 : ℝ) * (1 - 0.011))) ≤ 0.000598423559 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001406272470 / (12474 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598423559 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598423559 : ℝ) + 3.141593 * 0.053057589447 / (12474 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001210358365 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057589447)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406272470) : PiBarMP 12474 12 0.011 xi bn ≤ 0.162720335401 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12474 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037500299599 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.071085346277 : ℝ) ≤ √((12474 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.687062813917 : ℝ) ≤ √(12474 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12474) ≤ 0.124745050248 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037500299599 + 0.053057589447 * 1.772454 / (2 * (111.071085346277 : ℝ))) * (1 + 0.001210358365) +
        8 / (12474 * 111.687062813917) + 0.124745050248 := by gcongr
    _ ≤ (0.162720335401 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057589447)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406272470) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283305135336) :
    parallelOracle 12474 0.011 xi bn cd ≤ 0.163729613670 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12474 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12474 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493162730 : ℝ) ≤ plow 12474 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.687062813917 : ℝ) ≤ √(12474 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283305135336 : ℝ) / (2 * 0.560493162730 * 111.687062813917)) * 0.162720335401 +
        0.283305135336 ^ 2 / (2 * 0.560493162730 * 111.687062813917) := by gcongr
    _ ≤ (0.163729613670 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057589447) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406272470)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283305135336) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12474 12474 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493162730 : ℝ) ≤ plow 12474 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.687062813917 : ℝ) ≤ √(12474 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12474 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12474 Θ 1.22 ≤ 0.011873358173 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.687062813917 := by gcongr <;> linarith
      _ ≤ (0.011873358173 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12474 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12474 12474 0.011 ≤ 0.008558619697 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12474 12474 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12474 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12474 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12474 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12474 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163729613670 + 0.011873358173 + (0.008558619697 : ℝ) *
        (1 + 2 * (0.283305135336 + 0.011873358173) / (0.560493162730 * 111.687062813917))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12474]

end BstLean.Part269.N12474

/-! The original eight local profiles supply actual 12474 moment certificates. -/
namespace BstLean.Part269.N12474
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12474 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12474 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12474 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053057589447 ∧
    0 ≤ bN 12474 BstLean.Part154.csC (groupTheta g) ∧ bN 12474 BstLean.Part154.csC (groupTheta g) ≤ 0.001406272470 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12474 12474 0.011
      (momentAllowance 12474 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12474 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12474 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12474 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12474 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12474 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230342330993 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12474 0.011
      (momentAllowance 12474 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12474 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12474
/-! The actual computed-centre upper energy formula at 12474. -/
namespace BstLean.Part269.N12474
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12474

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12474
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12474)
open BstLean.Part268 (cell12474)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086179296547
  | 2 => 0.087135410839
  | 3 => 0.088091725968
  | 4 => 0.089050126217
  | 5 => 0.090012873842
  | 6 => 0.090982662963
  | 7 => 0.091962678130
  | 8 => 0.092956657520
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12474 12474 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12474 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003795409572 + 0.003362150420 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S4.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S4.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12474

/-! Actual upper energy certificates on all 43 source endpoints at 12474. -/
namespace BstLean.Part269.N12474
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12474)
open BstLean.Part268 (cell12474)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12474 (gMinus 12474) (1 - (cell12474 i).lower) ≤ 1 ∧
    energyUpper 12474 (gMinus 12474) (BstLean.Part211.gPlus 12474)
      (finiteEnergy 12474 12474 0.011) (1 - (cell12474 i).lower) ≤
      (cell12474 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨10,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨11,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨12,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨13,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨14,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨15,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨16,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨17,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨18,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨19,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨20,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨21,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨22,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨23,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨24,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨25,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨26,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨27,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨28,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨29,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨30,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨31,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨32,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨33,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨34,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨35,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨36,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨37,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨38,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨39,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨40,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨41,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨42,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨43,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨44,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨45,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨46,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨47,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨48,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨49,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨50,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨51,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12474) (by norm_num)
        (q := 1 - (cell12474 ⟨52,by decide⟩).lower)
        (by norm_num [cell12474]) (by norm_num [cell12474])
      exact ⟨E.1,E.2.trans (by norm_num [cell12474])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12474

/-! Source-cell containment and simple scalar guards at 12474. -/
namespace BstLean.Part269.N12474
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12474)
open BstLean.Part268 (cell12474)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12474 ⟨10,by decide⟩).lower ∧ (cell12474 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12474 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12474 ⟨11,by decide⟩).lower ∧ (cell12474 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12474 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12474 ⟨12,by decide⟩).lower ∧ (cell12474 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12474 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12474 ⟨13,by decide⟩).lower ∧ (cell12474 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12474 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12474 ⟨14,by decide⟩).lower ∧ (cell12474 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12474 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12474 ⟨15,by decide⟩).lower ∧ (cell12474 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12474 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12474 ⟨16,by decide⟩).lower ∧ (cell12474 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12474 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12474 ⟨17,by decide⟩).lower ∧ (cell12474 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12474 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12474 ⟨18,by decide⟩).lower ∧ (cell12474 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12474 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12474 ⟨19,by decide⟩).lower ∧ (cell12474 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12474 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12474 ⟨20,by decide⟩).lower ∧ (cell12474 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12474 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12474 ⟨21,by decide⟩).lower ∧ (cell12474 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12474 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12474 ⟨22,by decide⟩).lower ∧ (cell12474 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12474 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12474 ⟨23,by decide⟩).lower ∧ (cell12474 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12474 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12474 ⟨24,by decide⟩).lower ∧ (cell12474 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12474 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12474 ⟨25,by decide⟩).lower ∧ (cell12474 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12474 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12474 ⟨26,by decide⟩).lower ∧ (cell12474 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12474 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12474 ⟨27,by decide⟩).lower ∧ (cell12474 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12474 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12474 ⟨28,by decide⟩).lower ∧ (cell12474 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12474 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12474 ⟨29,by decide⟩).lower ∧ (cell12474 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12474 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12474 ⟨30,by decide⟩).lower ∧ (cell12474 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12474 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12474 ⟨31,by decide⟩).lower ∧ (cell12474 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12474 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12474 ⟨32,by decide⟩).lower ∧ (cell12474 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12474 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12474 ⟨33,by decide⟩).lower ∧ (cell12474 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12474 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12474 ⟨34,by decide⟩).lower ∧ (cell12474 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12474 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12474 ⟨35,by decide⟩).lower ∧ (cell12474 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12474 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12474 ⟨36,by decide⟩).lower ∧ (cell12474 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12474 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12474 ⟨37,by decide⟩).lower ∧ (cell12474 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12474 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12474 ⟨38,by decide⟩).lower ∧ (cell12474 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12474 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12474 ⟨39,by decide⟩).lower ∧ (cell12474 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12474 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12474 ⟨40,by decide⟩).lower ∧ (cell12474 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12474 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12474 ⟨41,by decide⟩).lower ∧ (cell12474 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12474 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12474 ⟨42,by decide⟩).lower ∧ (cell12474 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12474 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12474 ⟨43,by decide⟩).lower ∧ (cell12474 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12474 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12474 ⟨44,by decide⟩).lower ∧ (cell12474 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12474 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12474 ⟨45,by decide⟩).lower ∧ (cell12474 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12474 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12474 ⟨46,by decide⟩).lower ∧ (cell12474 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12474 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12474 ⟨47,by decide⟩).lower ∧ (cell12474 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12474 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12474 ⟨48,by decide⟩).lower ∧ (cell12474 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12474 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12474 ⟨49,by decide⟩).lower ∧ (cell12474 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12474 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12474 ⟨50,by decide⟩).lower ∧ (cell12474 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12474 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12474 ⟨51,by decide⟩).lower ∧ (cell12474 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12474 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12474 ⟨52,by decide⟩).lower ∧ (cell12474 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12474 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12474 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12474 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12474,cell12474,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12474 i).lower ∧
    (cell12474 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12474 i).upper ≤ (0.532 : ℝ) ∧
    (cell12474 i).centre ≤ (0.1 : ℝ) ∧ (cell12474 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12474 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12474 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12474

/-! The local source numeric instances at 12474 have no network premises. -/
namespace BstLean.Part269.N12474
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12474)
open BstLean.Part268 (cell12474)

noncomputable def sourceNumerics12474 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12474 (cell12474 i)
      scalarRow12474.M scalarRow12474.H scalarRow12474.xi := by
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
    energy_allowance := scalarRow12474.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12474]
    centre_nonneg := (scalarRow12474.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12474])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12474