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
/-! Actual 12450 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12450
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12450 ≤ (1.036170142337 : ℝ) := by
  have hr : (111.579568022106 : ℝ) ≤ √(12450 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.579568022106 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12450 12450 (11 / 1000) ≤
    (0.008566865062 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12450) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.579568022106 : ℝ) ≤ √(12450 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12450)
  have hdiv : K / √(12450 : ℝ) ≤ K / 111.579568022106 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.579568022106 ≤ (0.008566865062 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12450.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12450 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12450 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12450 := gPlus_lower 12450
end BstLean.Part269.N12450

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12450
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036170142336 : ℝ) ≤ wn 12450 := by
  have hn : √(12450 : ℝ) ≤ 111.579568022107 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12450 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.579568022107 ≤ 2 / √(12450 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257028246 : ℝ) ≤ rhoBar 12450 BstLean.Part154.csC ∧
    rhoBar 12450 BstLean.Part154.csC ≤ 0.000257028644 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036170142336 : ℝ) / (1.295212 * 12450) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036170142337 : ℝ) / (1.29521 * 12450) := by gcongr
      _ ≤ (0.000257028644 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12450 BstLean.Part154.csC) ≤ 0.001028180640 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12450 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12450 BstLean.Part154.csC) (piBar (rhoBar 12450 BstLean.Part154.csC)) ≤ 0.000196320399 ∧
    cc1 (rhoBar 12450 BstLean.Part154.csC) (piBar (rhoBar 12450 BstLean.Part154.csC)) ≤ 0.000124919935 ∧
    cc2 (rhoBar 12450 BstLean.Part154.csC) ≤ 0.000072516933 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12450 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12450 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12450 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12450 BstLean.Part154.csC * nuR (rhoBar 12450 BstLean.Part154.csC)) ≤ 0.000514073804 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257028644 : ℝ) * 0.001028180640 := by gcongr
      _ ≤ (0.000514073804 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12450 BstLean.Part154.csC) * nuR (rhoBar 12450 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001028180640 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12450 BstLean.Part154.csC) * rhoBar 12450 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257028644 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257028644 / 2 + 0.399 * 0.001028180640 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196320399 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514073804 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124919935 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257028644 / 1.414213562 := by gcongr
      _ ≤ (0.000072516933 : ℝ) := by norm_num

end BstLean.Part269.N12450

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12450
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12450 BstLean.Part154.csC) (piBar (rhoBar 12450 BstLean.Part154.csC)) ≤ 1.66443E-7 := by
  have hr0 : 0 ≤ rhoBar 12450 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12450 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12450 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12450 BstLean.Part154.csC) (piBar (rhoBar 12450 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12450 BstLean.Part154.csC) (piBar (rhoBar 12450 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12450 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196320399 : ℝ) ^ 2 + 0.000124919935 ^ 2 + 3 * 0.000072516933 ^ 2 +
        2 * 0.797885 * 0.000196320399 * 0.000124919935 + 2 * 0.000196320399 * 0.000072516933 +
        4 * 0.797885 * 0.000124919935 * 0.000072516933 := by gcongr
    _ ≤ (1.66443E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12450 BstLean.Part154.csC Θ ≤ 0.002683958199 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12450 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12450 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12450 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12450 BstLean.Part154.csC) (piBar (rhoBar 12450 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12450 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036170142337 * 1.66443E-7 / (0.000257028246 : ℝ) := by gcongr
    _ ≤ 0.002683958199 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12450 BstLean.Part154.csC Θ ≤ 0.002979034826 + 0.000678192221 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12450 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12450 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12450 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036170142337 : ℝ) * ((2 * Θ * 0.000257028644 +
        (6863 / 10000) * 0.000257028644 * 12450 * 0.001028180640) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002979034826 + 0.000678192221 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12450 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12450 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12450 0.011 Θ ∧ gammaRatio 12450 0.011 Θ ≤ 0.000088359802 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12450 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036170142337 : ℝ) * 0.525 / ((1 - 0.011) * 12450) := by gcongr
      _ ≤ (0.000088359802 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12450 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12450 0.011 Θ) :=
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
    badAllowance 12450 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12450 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12450 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12450 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12450 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12450 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12450 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12450 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12450 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12450 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12450 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036170142337 : ℝ) * 12450 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12450 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003795409572 + 0.003362150420 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12450

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12450
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12450 BstLean.Part154.csC) (piBar (rhoBar 12450 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12450 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12450 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12450 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12450 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12450 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12450 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12450 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12450 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12450 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12450 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12450 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12450 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12450 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12450 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053014386999 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12450) ≤ 0.010703013126 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12450 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036170142337)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010703013126 + 2 * 0.737676 / 12450) := by gcongr
    _ ≤ (0.053014386999 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12450 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12450

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12450
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492035526 : ℝ) ≤ plow 12450 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12450) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053067138543)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409078055) : eMP 12450 0.011 xi bn ≤ 0.001212734319 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12450 : ℝ) * (1 - 0.011))) ≤ 0.000599597295 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001409078055 / (12450 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599597295 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599597295 : ℝ) + 3.141593 * 0.053067138543 / (12450 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001212734319 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053067138543)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409078055) : PiBarMP 12450 12 0.011 xi bn ≤ 0.162878539324 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12450 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037537688462 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.964183410684 : ℝ) ≤ √((12450 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.579568022106 : ℝ) ≤ √(12450 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12450) ≤ 0.124865228552 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037537688462 + 0.053067138543 * 1.772454 / (2 * (110.964183410684 : ℝ))) * (1 + 0.001212734319) +
        8 / (12450 * 111.579568022106) + 0.124865228552 := by gcongr
    _ ≤ (0.162878539324 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053067138543)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409078055) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283377445112) :
    parallelOracle 12450 0.011 xi bn cd ≤ 0.163889572058 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12450 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12450 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492035526 : ℝ) ≤ plow 12450 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.579568022106 : ℝ) ≤ √(12450 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283377445112 : ℝ) / (2 * 0.560492035526 * 111.579568022106)) * 0.162878539324 +
        0.283377445112 ^ 2 / (2 * 0.560492035526 * 111.579568022106) := by gcongr
    _ ≤ (0.163889572058 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053067138543) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001409078055)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283377445112) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12450 12450 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492035526 : ℝ) ≤ plow 12450 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.579568022106 : ℝ) ≤ √(12450 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12450 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12450 Θ 1.22 ≤ 0.011884796863 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.579568022106 := by gcongr <;> linarith
      _ ≤ (0.011884796863 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12450 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12450 12450 0.011 ≤ 0.008566865062 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12450 12450 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12450 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12450 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12450 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12450 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163889572058 + 0.011884796863 + (0.008566865062 : ℝ) *
        (1 + 2 * (0.283377445112 + 0.011884796863) / (0.560492035526 * 111.579568022106))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12450]

end BstLean.Part269.N12450

/-! The original eight local profiles supply actual 12450 moment certificates. -/
namespace BstLean.Part269.N12450
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12450 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12450 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12450 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053067138543 ∧
    0 ≤ bN 12450 BstLean.Part154.csC (groupTheta g) ∧ bN 12450 BstLean.Part154.csC (groupTheta g) ≤ 0.001409078055 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12450 12450 0.011
      (momentAllowance 12450 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12450 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12450 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12450 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12450 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12450 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230363058113 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12450 0.011
      (momentAllowance 12450 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12450 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12450
/-! The actual computed-centre upper energy formula at 12450. -/
namespace BstLean.Part269.N12450
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12450

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12450
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12450)
open BstLean.Part268 (cell12450)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086256309122
  | 2 => 0.087214007287
  | 3 => 0.088172163698
  | 4 => 0.089132719811
  | 5 => 0.090098004771
  | 6 => 0.091070790452
  | 7 => 0.092054351206
  | 8 => 0.093052528301
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12450 12450 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12450 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12450

/-! Actual upper energy certificates on all 43 source endpoints at 12450. -/
namespace BstLean.Part269.N12450
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12450)
open BstLean.Part268 (cell12450)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12450 (gMinus 12450) (1 - (cell12450 i).lower) ≤ 1 ∧
    energyUpper 12450 (gMinus 12450) (BstLean.Part211.gPlus 12450)
      (finiteEnergy 12450 12450 0.011) (1 - (cell12450 i).lower) ≤
      (cell12450 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨10,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨11,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨12,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨13,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨14,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨15,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨16,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨17,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨18,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨19,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨20,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨21,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨22,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨23,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨24,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨25,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨26,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨27,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨28,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨29,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨30,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨31,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨32,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨33,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨34,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨35,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨36,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨37,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨38,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨39,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨40,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨41,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨42,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨43,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨44,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨45,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨46,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨47,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨48,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨49,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨50,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨51,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12450) (by norm_num)
        (q := 1 - (cell12450 ⟨52,by decide⟩).lower)
        (by norm_num [cell12450]) (by norm_num [cell12450])
      exact ⟨E.1,E.2.trans (by norm_num [cell12450])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12450

/-! Source-cell containment and simple scalar guards at 12450. -/
namespace BstLean.Part269.N12450
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12450)
open BstLean.Part268 (cell12450)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12450 ⟨10,by decide⟩).lower ∧ (cell12450 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12450 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12450 ⟨11,by decide⟩).lower ∧ (cell12450 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12450 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12450 ⟨12,by decide⟩).lower ∧ (cell12450 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12450 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12450 ⟨13,by decide⟩).lower ∧ (cell12450 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12450 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12450 ⟨14,by decide⟩).lower ∧ (cell12450 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12450 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12450 ⟨15,by decide⟩).lower ∧ (cell12450 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12450 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12450 ⟨16,by decide⟩).lower ∧ (cell12450 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12450 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12450 ⟨17,by decide⟩).lower ∧ (cell12450 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12450 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12450 ⟨18,by decide⟩).lower ∧ (cell12450 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12450 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12450 ⟨19,by decide⟩).lower ∧ (cell12450 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12450 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12450 ⟨20,by decide⟩).lower ∧ (cell12450 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12450 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12450 ⟨21,by decide⟩).lower ∧ (cell12450 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12450 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12450 ⟨22,by decide⟩).lower ∧ (cell12450 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12450 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12450 ⟨23,by decide⟩).lower ∧ (cell12450 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12450 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12450 ⟨24,by decide⟩).lower ∧ (cell12450 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12450 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12450 ⟨25,by decide⟩).lower ∧ (cell12450 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12450 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12450 ⟨26,by decide⟩).lower ∧ (cell12450 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12450 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12450 ⟨27,by decide⟩).lower ∧ (cell12450 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12450 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12450 ⟨28,by decide⟩).lower ∧ (cell12450 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12450 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12450 ⟨29,by decide⟩).lower ∧ (cell12450 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12450 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12450 ⟨30,by decide⟩).lower ∧ (cell12450 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12450 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12450 ⟨31,by decide⟩).lower ∧ (cell12450 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12450 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12450 ⟨32,by decide⟩).lower ∧ (cell12450 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12450 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12450 ⟨33,by decide⟩).lower ∧ (cell12450 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12450 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12450 ⟨34,by decide⟩).lower ∧ (cell12450 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12450 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12450 ⟨35,by decide⟩).lower ∧ (cell12450 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12450 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12450 ⟨36,by decide⟩).lower ∧ (cell12450 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12450 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12450 ⟨37,by decide⟩).lower ∧ (cell12450 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12450 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12450 ⟨38,by decide⟩).lower ∧ (cell12450 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12450 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12450 ⟨39,by decide⟩).lower ∧ (cell12450 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12450 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12450 ⟨40,by decide⟩).lower ∧ (cell12450 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12450 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12450 ⟨41,by decide⟩).lower ∧ (cell12450 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12450 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12450 ⟨42,by decide⟩).lower ∧ (cell12450 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12450 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12450 ⟨43,by decide⟩).lower ∧ (cell12450 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12450 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12450 ⟨44,by decide⟩).lower ∧ (cell12450 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12450 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12450 ⟨45,by decide⟩).lower ∧ (cell12450 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12450 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12450 ⟨46,by decide⟩).lower ∧ (cell12450 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12450 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12450 ⟨47,by decide⟩).lower ∧ (cell12450 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12450 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12450 ⟨48,by decide⟩).lower ∧ (cell12450 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12450 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12450 ⟨49,by decide⟩).lower ∧ (cell12450 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12450 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12450 ⟨50,by decide⟩).lower ∧ (cell12450 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12450 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12450 ⟨51,by decide⟩).lower ∧ (cell12450 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12450 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12450 ⟨52,by decide⟩).lower ∧ (cell12450 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12450 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12450 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12450 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12450,cell12450,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12450 i).lower ∧
    (cell12450 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12450 i).upper ≤ (0.532 : ℝ) ∧
    (cell12450 i).centre ≤ (0.1 : ℝ) ∧ (cell12450 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12450 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12450 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12450

/-! The local source numeric instances at 12450 have no network premises. -/
namespace BstLean.Part269.N12450
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12450)
open BstLean.Part268 (cell12450)

noncomputable def sourceNumerics12450 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12450 (cell12450 i)
      scalarRow12450.M scalarRow12450.H scalarRow12450.xi := by
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
    energy_allowance := scalarRow12450.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12450]
    centre_nonneg := (scalarRow12450.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12450])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12450
/-! Actual 12451 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12451
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12451 ≤ (1.036168676907 : ℝ) := by
  have hr : (111.584049039278 : ℝ) ≤ √(12451 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.584049039278 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12451 12451 (11 / 1000) ≤
    (0.008566521029 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12451) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.584049039278 : ℝ) ≤ √(12451 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12451)
  have hdiv : K / √(12451 : ℝ) ≤ K / 111.584049039278 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.584049039278 ≤ (0.008566521029 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12451.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12451 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12451 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12451 := gPlus_lower 12451
end BstLean.Part269.N12451

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12451
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036168676906 : ℝ) ≤ wn 12451 := by
  have hn : √(12451 : ℝ) ≤ 111.584049039279 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12451 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.584049039279 ≤ 2 / √(12451 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257007240 : ℝ) ≤ rhoBar 12451 BstLean.Part154.csC ∧
    rhoBar 12451 BstLean.Part154.csC ≤ 0.000257007638 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036168676906 : ℝ) / (1.295212 * 12451) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036168676907 : ℝ) / (1.29521 * 12451) := by gcongr
      _ ≤ (0.000257007638 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12451 BstLean.Part154.csC) ≤ 0.001028096605 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12451 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12451 BstLean.Part154.csC) (piBar (rhoBar 12451 BstLean.Part154.csC)) ≤ 0.000196304354 ∧
    cc1 (rhoBar 12451 BstLean.Part154.csC) (piBar (rhoBar 12451 BstLean.Part154.csC)) ≤ 0.000124909725 ∧
    cc2 (rhoBar 12451 BstLean.Part154.csC) ≤ 0.000072511006 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12451 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12451 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12451 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12451 BstLean.Part154.csC * nuR (rhoBar 12451 BstLean.Part154.csC)) ≤ 0.000514031789 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257007638 : ℝ) * 0.001028096605 := by gcongr
      _ ≤ (0.000514031789 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12451 BstLean.Part154.csC) * nuR (rhoBar 12451 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001028096605 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12451 BstLean.Part154.csC) * rhoBar 12451 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257007638 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257007638 / 2 + 0.399 * 0.001028096605 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196304354 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000514031789 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124909725 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257007638 / 1.414213562 := by gcongr
      _ ≤ (0.000072511006 : ℝ) := by norm_num

end BstLean.Part269.N12451

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12451
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12451 BstLean.Part154.csC) (piBar (rhoBar 12451 BstLean.Part154.csC)) ≤ 1.66416E-7 := by
  have hr0 : 0 ≤ rhoBar 12451 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12451 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12451 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12451 BstLean.Part154.csC) (piBar (rhoBar 12451 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12451 BstLean.Part154.csC) (piBar (rhoBar 12451 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12451 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196304354 : ℝ) ^ 2 + 0.000124909725 ^ 2 + 3 * 0.000072511006 ^ 2 +
        2 * 0.797885 * 0.000196304354 * 0.000124909725 + 2 * 0.000196304354 * 0.000072511006 +
        4 * 0.797885 * 0.000124909725 * 0.000072511006 := by gcongr
    _ ≤ (1.66416E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12451 BstLean.Part154.csC Θ ≤ 0.002683738350 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12451 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12451 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12451 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12451 BstLean.Part154.csC) (piBar (rhoBar 12451 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12451 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036168676907 * 1.66416E-7 / (0.000257007240 : ℝ) := by gcongr
    _ ≤ 0.002683738350 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12451 BstLean.Part154.csC Θ ≤ 0.002978782927 + 0.000678135835 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12451 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12451 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12451 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036168676907 : ℝ) * ((2 * Θ * 0.000257007638 +
        (6863 / 10000) * 0.000257007638 * 12451 * 0.001028096605) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002978782927 + 0.000678135835 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12451 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12451 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12451 0.011 Θ ∧ gammaRatio 12451 0.011 Θ ≤ 0.000088352580 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12451 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036168676907 : ℝ) * 0.525 / ((1 - 0.011) * 12451) := by gcongr
      _ ≤ (0.000088352580 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12451 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12451 0.011 Θ) :=
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
    badAllowance 12451 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12451 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12451 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12451 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12451 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12451 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12451 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12451 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12451 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12451 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12451 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036168676907 : ℝ) * 12451 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12451 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003795157673 + 0.003361874185 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12451

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12451
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12451 BstLean.Part154.csC) (piBar (rhoBar 12451 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12451 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12451 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12451 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12451 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12451 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12451 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12451 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12451 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12451 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12451 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12451 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12451 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12451 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12451 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053012234723 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12451) ≤ 0.010702583312 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12451 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036168676907)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010702583312 + 2 * 0.737676 / 12451) := by gcongr
    _ ≤ (0.053012234723 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12451 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12451

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12451
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492082579 : ℝ) ≤ plow 12451 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12451) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053066741621)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408962634) : eMP 12451 0.011 xi bn ≤ 0.001212635858 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12451 : ℝ) * (1 - 0.011))) ≤ 0.000599548659 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001408962634 / (12451 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599548659 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599548659 : ℝ) + 3.141593 * 0.053066741621 / (12451 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001212635858 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053066741621)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408962634) : PiBarMP 12451 12 0.011 xi bn ≤ 0.162871961015 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12451 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037536151029 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.968639714110 : ℝ) ≤ √((12451 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.584049039278 : ℝ) ≤ √(12451 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12451) ≤ 0.124860214186 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037536151029 + 0.053066741621 * 1.772454 / (2 * (110.968639714110 : ℝ))) * (1 + 0.001212635858) +
        8 / (12451 * 111.584049039278) + 0.124860214186 := by gcongr
    _ ≤ (0.162871961015 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053066741621)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408962634) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283374431321) :
    parallelOracle 12451 0.011 xi bn cd ≤ 0.163882920580 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12451 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12451 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492082579 : ℝ) ≤ plow 12451 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.584049039278 : ℝ) ≤ √(12451 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283374431321 : ℝ) / (2 * 0.560492082579 * 111.584049039278)) * 0.162871961015 +
        0.283374431321 ^ 2 / (2 * 0.560492082579 * 111.584049039278) := by gcongr
    _ ≤ (0.163882920580 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053066741621) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408962634)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283374431321) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12451 12451 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492082579 : ℝ) ≤ plow 12451 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.584049039278 : ℝ) ≤ √(12451 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12451 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12451 Θ 1.22 ≤ 0.011884319591 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.584049039278 := by gcongr <;> linarith
      _ ≤ (0.011884319591 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12451 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12451 12451 0.011 ≤ 0.008566521029 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12451 12451 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12451 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12451 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12451 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12451 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163882920580 + 0.011884319591 + (0.008566521029 : ℝ) *
        (1 + 2 * (0.283374431321 + 0.011884319591) / (0.560492082579 * 111.584049039278))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12451]

end BstLean.Part269.N12451

/-! The original eight local profiles supply actual 12451 moment certificates. -/
namespace BstLean.Part269.N12451
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12451 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12451 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12451 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053066741621 ∧
    0 ≤ bN 12451 BstLean.Part154.csC (groupTheta g) ∧ bN 12451 BstLean.Part154.csC (groupTheta g) ≤ 0.001408962634 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12451 12451 0.011
      (momentAllowance 12451 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12451 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12451 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12451 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12451 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12451 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230362196598 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12451 0.011
      (momentAllowance 12451 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12451 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12451
/-! The actual computed-centre upper energy formula at 12451. -/
namespace BstLean.Part269.N12451
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12451

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12451
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12451)
open BstLean.Part268 (cell12451)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086253084217
  | 2 => 0.087210715685
  | 3 => 0.088168794511
  | 4 => 0.089129259735
  | 5 => 0.090094437679
  | 6 => 0.091067096935
  | 7 => 0.092050508064
  | 8 => 0.093048507987
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12451 12451 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12451 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12451

/-! Actual upper energy certificates on all 43 source endpoints at 12451. -/
namespace BstLean.Part269.N12451
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12451)
open BstLean.Part268 (cell12451)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12451 (gMinus 12451) (1 - (cell12451 i).lower) ≤ 1 ∧
    energyUpper 12451 (gMinus 12451) (BstLean.Part211.gPlus 12451)
      (finiteEnergy 12451 12451 0.011) (1 - (cell12451 i).lower) ≤
      (cell12451 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨10,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨11,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨12,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨13,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨14,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨15,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨16,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨17,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨18,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨19,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨20,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨21,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨22,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨23,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨24,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨25,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨26,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨27,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨28,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨29,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨30,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨31,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨32,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨33,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨34,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨35,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨36,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨37,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨38,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨39,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨40,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨41,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨42,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨43,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨44,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨45,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨46,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨47,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨48,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨49,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨50,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨51,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12451) (by norm_num)
        (q := 1 - (cell12451 ⟨52,by decide⟩).lower)
        (by norm_num [cell12451]) (by norm_num [cell12451])
      exact ⟨E.1,E.2.trans (by norm_num [cell12451])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12451

/-! Source-cell containment and simple scalar guards at 12451. -/
namespace BstLean.Part269.N12451
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12451)
open BstLean.Part268 (cell12451)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12451 ⟨10,by decide⟩).lower ∧ (cell12451 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12451 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12451 ⟨11,by decide⟩).lower ∧ (cell12451 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12451 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12451 ⟨12,by decide⟩).lower ∧ (cell12451 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12451 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12451 ⟨13,by decide⟩).lower ∧ (cell12451 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12451 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12451 ⟨14,by decide⟩).lower ∧ (cell12451 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12451 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12451 ⟨15,by decide⟩).lower ∧ (cell12451 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12451 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12451 ⟨16,by decide⟩).lower ∧ (cell12451 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12451 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12451 ⟨17,by decide⟩).lower ∧ (cell12451 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12451 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12451 ⟨18,by decide⟩).lower ∧ (cell12451 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12451 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12451 ⟨19,by decide⟩).lower ∧ (cell12451 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12451 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12451 ⟨20,by decide⟩).lower ∧ (cell12451 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12451 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12451 ⟨21,by decide⟩).lower ∧ (cell12451 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12451 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12451 ⟨22,by decide⟩).lower ∧ (cell12451 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12451 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12451 ⟨23,by decide⟩).lower ∧ (cell12451 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12451 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12451 ⟨24,by decide⟩).lower ∧ (cell12451 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12451 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12451 ⟨25,by decide⟩).lower ∧ (cell12451 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12451 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12451 ⟨26,by decide⟩).lower ∧ (cell12451 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12451 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12451 ⟨27,by decide⟩).lower ∧ (cell12451 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12451 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12451 ⟨28,by decide⟩).lower ∧ (cell12451 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12451 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12451 ⟨29,by decide⟩).lower ∧ (cell12451 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12451 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12451 ⟨30,by decide⟩).lower ∧ (cell12451 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12451 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12451 ⟨31,by decide⟩).lower ∧ (cell12451 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12451 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12451 ⟨32,by decide⟩).lower ∧ (cell12451 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12451 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12451 ⟨33,by decide⟩).lower ∧ (cell12451 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12451 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12451 ⟨34,by decide⟩).lower ∧ (cell12451 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12451 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12451 ⟨35,by decide⟩).lower ∧ (cell12451 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12451 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12451 ⟨36,by decide⟩).lower ∧ (cell12451 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12451 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12451 ⟨37,by decide⟩).lower ∧ (cell12451 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12451 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12451 ⟨38,by decide⟩).lower ∧ (cell12451 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12451 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12451 ⟨39,by decide⟩).lower ∧ (cell12451 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12451 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12451 ⟨40,by decide⟩).lower ∧ (cell12451 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12451 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12451 ⟨41,by decide⟩).lower ∧ (cell12451 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12451 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12451 ⟨42,by decide⟩).lower ∧ (cell12451 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12451 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12451 ⟨43,by decide⟩).lower ∧ (cell12451 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12451 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12451 ⟨44,by decide⟩).lower ∧ (cell12451 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12451 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12451 ⟨45,by decide⟩).lower ∧ (cell12451 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12451 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12451 ⟨46,by decide⟩).lower ∧ (cell12451 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12451 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12451 ⟨47,by decide⟩).lower ∧ (cell12451 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12451 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12451 ⟨48,by decide⟩).lower ∧ (cell12451 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12451 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12451 ⟨49,by decide⟩).lower ∧ (cell12451 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12451 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12451 ⟨50,by decide⟩).lower ∧ (cell12451 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12451 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12451 ⟨51,by decide⟩).lower ∧ (cell12451 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12451 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12451 ⟨52,by decide⟩).lower ∧ (cell12451 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12451 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12451 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12451 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12451,cell12451,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12451 i).lower ∧
    (cell12451 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12451 i).upper ≤ (0.532 : ℝ) ∧
    (cell12451 i).centre ≤ (0.1 : ℝ) ∧ (cell12451 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12451 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12451 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12451

/-! The local source numeric instances at 12451 have no network premises. -/
namespace BstLean.Part269.N12451
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12451)
open BstLean.Part268 (cell12451)

noncomputable def sourceNumerics12451 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12451 (cell12451 i)
      scalarRow12451.M scalarRow12451.H scalarRow12451.xi := by
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
    energy_allowance := scalarRow12451.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12451]
    centre_nonneg := (scalarRow12451.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12451])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12451
/-! Actual 12452 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12452
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12452 ≤ (1.036167211654 : ℝ) := by
  have hr : (111.588529876506 : ℝ) ≤ √(12452 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.588529876506 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12452 12452 (11 / 1000) ≤
    (0.008566177038 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12452) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.588529876506 : ℝ) ≤ √(12452 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12452)
  have hdiv : K / √(12452 : ℝ) ≤ K / 111.588529876506 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.588529876506 ≤ (0.008566177038 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12452.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12452 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12452 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12452 := gPlus_lower 12452
end BstLean.Part269.N12452

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12452
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036167211653 : ℝ) ≤ wn 12452 := by
  have hn : √(12452 : ℝ) ≤ 111.588529876507 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12452 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.588529876507 ≤ 2 / √(12452 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256986237 : ℝ) ≤ rhoBar 12452 BstLean.Part154.csC ∧
    rhoBar 12452 BstLean.Part154.csC ≤ 0.000256986634 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036167211653 : ℝ) / (1.295212 * 12452) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036167211654 : ℝ) / (1.29521 * 12452) := by gcongr
      _ ≤ (0.000256986634 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12452 BstLean.Part154.csC) ≤ 0.001028012579 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12452 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12452 BstLean.Part154.csC) (piBar (rhoBar 12452 BstLean.Part154.csC)) ≤ 0.000196288310 ∧
    cc1 (rhoBar 12452 BstLean.Part154.csC) (piBar (rhoBar 12452 BstLean.Part154.csC)) ≤ 0.000124899517 ∧
    cc2 (rhoBar 12452 BstLean.Part154.csC) ≤ 0.000072505080 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12452 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12452 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12452 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12452 BstLean.Part154.csC * nuR (rhoBar 12452 BstLean.Part154.csC)) ≤ 0.000513989779 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256986634 : ℝ) * 0.001028012579 := by gcongr
      _ ≤ (0.000513989779 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12452 BstLean.Part154.csC) * nuR (rhoBar 12452 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001028012579 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12452 BstLean.Part154.csC) * rhoBar 12452 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256986634 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256986634 / 2 + 0.399 * 0.001028012579 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196288310 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513989779 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124899517 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256986634 / 1.414213562 := by gcongr
      _ ≤ (0.000072505080 : ℝ) := by norm_num

end BstLean.Part269.N12452

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12452
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12452 BstLean.Part154.csC) (piBar (rhoBar 12452 BstLean.Part154.csC)) ≤ 1.66389E-7 := by
  have hr0 : 0 ≤ rhoBar 12452 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12452 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12452 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12452 BstLean.Part154.csC) (piBar (rhoBar 12452 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12452 BstLean.Part154.csC) (piBar (rhoBar 12452 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12452 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196288310 : ℝ) ^ 2 + 0.000124899517 ^ 2 + 3 * 0.000072505080 ^ 2 +
        2 * 0.797885 * 0.000196288310 * 0.000124899517 + 2 * 0.000196288310 * 0.000072505080 +
        4 * 0.797885 * 0.000124899517 * 0.000072505080 := by gcongr
    _ ≤ (1.66389E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12452 BstLean.Part154.csC Θ ≤ 0.002683518436 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12452 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12452 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12452 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12452 BstLean.Part154.csC) (piBar (rhoBar 12452 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12452 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036167211654 * 1.66389E-7 / (0.000256986237 : ℝ) := by gcongr
    _ ≤ 0.002683518436 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12452 BstLean.Part154.csC Θ ≤ 0.002978531039 + 0.000678079456 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12452 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12452 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12452 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036167211654 : ℝ) * ((2 * Θ * 0.000256986634 +
        (6863 / 10000) * 0.000256986634 * 12452 * 0.001028012579) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002978531039 + 0.000678079456 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12452 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12452 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12452 0.011 Θ ∧ gammaRatio 12452 0.011 Θ ≤ 0.000088345360 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12452 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036167211654 : ℝ) * 0.525 / ((1 - 0.011) * 12452) := by gcongr
      _ ≤ (0.000088345360 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12452 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12452 0.011 Θ) :=
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
    badAllowance 12452 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12452 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12452 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12452 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12452 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12452 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12452 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12452 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12452 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12452 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12452 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036167211654 : ℝ) * 12452 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12452 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003794905785 + 0.003361597892 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12452

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12452
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12452 BstLean.Part154.csC) (piBar (rhoBar 12452 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12452 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12452 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12452 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12452 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12452 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12452 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12452 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12452 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12452 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12452 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12452 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12452 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12452 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12452 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053010082709 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12452) ≤ 0.010702153550 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12452 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036167211654)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010702153550 + 2 * 0.737676 / 12452) := by gcongr
    _ ≤ (0.053010082709 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12452 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12452

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12452
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492129625 : ℝ) ≤ plow 12452 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12452) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053066344679)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408847179) : eMP 12452 0.011 xi bn ≤ 0.001212537392 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12452 : ℝ) * (1 - 0.011))) ≤ 0.000599500020 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001408847179 / (12452 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599500020 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599500020 : ℝ) + 3.141593 * 0.053066344679 / (12452 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001212537392 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053066344679)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408847179) : PiBarMP 12452 12 0.011 xi bn ≤ 0.162865382796 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12452 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037534613080 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.973095838586 : ℝ) ≤ √((12452 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.588529876506 : ℝ) ≤ √(12452 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12452) ≤ 0.124855200425 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037534613080 + 0.053066344679 * 1.772454 / (2 * (110.973095838586 : ℝ))) * (1 + 0.001212537392) +
        8 / (12452 * 111.588529876506) + 0.124855200425 := by gcongr
    _ ≤ (0.162865382796 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053066344679)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408847179) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283371417744) :
    parallelOracle 12452 0.011 xi bn cd ≤ 0.163876269201 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12452 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12452 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492129625 : ℝ) ≤ plow 12452 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.588529876506 : ℝ) ≤ √(12452 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283371417744 : ℝ) / (2 * 0.560492129625 * 111.588529876506)) * 0.162865382796 +
        0.283371417744 ^ 2 / (2 * 0.560492129625 * 111.588529876506) := by gcongr
    _ ≤ (0.163876269201 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053066344679) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408847179)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283371417744) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12452 12452 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492129625 : ℝ) ≤ plow 12452 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.588529876506 : ℝ) ≤ √(12452 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12452 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12452 Θ 1.22 ≤ 0.011883842376 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.588529876506 := by gcongr <;> linarith
      _ ≤ (0.011883842376 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12452 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12452 12452 0.011 ≤ 0.008566177038 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12452 12452 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12452 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12452 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12452 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12452 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163876269201 + 0.011883842376 + (0.008566177038 : ℝ) *
        (1 + 2 * (0.283371417744 + 0.011883842376) / (0.560492129625 * 111.588529876506))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12452]

end BstLean.Part269.N12452

/-! The original eight local profiles supply actual 12452 moment certificates. -/
namespace BstLean.Part269.N12452
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12452 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12452 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12452 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053066344679 ∧
    0 ≤ bN 12452 BstLean.Part154.csC (groupTheta g) ∧ bN 12452 BstLean.Part154.csC (groupTheta g) ≤ 0.001408847179 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12452 12452 0.011
      (momentAllowance 12452 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12452 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12452 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12452 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12452 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12452 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230361335035 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12452 0.011
      (momentAllowance 12452 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12452 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12452
/-! The actual computed-centre upper energy formula at 12452. -/
namespace BstLean.Part269.N12452
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12452

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12452
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12452)
open BstLean.Part268 (cell12452)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086249860718
  | 2 => 0.087207425551
  | 3 => 0.088165426868
  | 4 => 0.089125801296
  | 5 => 0.090090872338
  | 6 => 0.091063405305
  | 7 => 0.092046666977
  | 8 => 0.093044489927
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12452 12452 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12452 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12452

/-! Actual upper energy certificates on all 43 source endpoints at 12452. -/
namespace BstLean.Part269.N12452
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12452)
open BstLean.Part268 (cell12452)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12452 (gMinus 12452) (1 - (cell12452 i).lower) ≤ 1 ∧
    energyUpper 12452 (gMinus 12452) (BstLean.Part211.gPlus 12452)
      (finiteEnergy 12452 12452 0.011) (1 - (cell12452 i).lower) ≤
      (cell12452 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨10,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨11,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨12,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨13,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨14,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨15,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨16,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨17,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨18,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨19,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨20,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨21,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨22,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨23,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨24,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨25,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨26,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨27,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨28,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨29,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨30,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨31,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨32,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨33,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨34,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨35,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨36,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨37,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨38,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨39,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨40,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨41,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨42,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨43,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨44,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨45,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨46,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨47,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨48,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨49,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨50,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨51,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12452) (by norm_num)
        (q := 1 - (cell12452 ⟨52,by decide⟩).lower)
        (by norm_num [cell12452]) (by norm_num [cell12452])
      exact ⟨E.1,E.2.trans (by norm_num [cell12452])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12452

/-! Source-cell containment and simple scalar guards at 12452. -/
namespace BstLean.Part269.N12452
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12452)
open BstLean.Part268 (cell12452)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12452 ⟨10,by decide⟩).lower ∧ (cell12452 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12452 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12452 ⟨11,by decide⟩).lower ∧ (cell12452 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12452 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12452 ⟨12,by decide⟩).lower ∧ (cell12452 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12452 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12452 ⟨13,by decide⟩).lower ∧ (cell12452 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12452 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12452 ⟨14,by decide⟩).lower ∧ (cell12452 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12452 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12452 ⟨15,by decide⟩).lower ∧ (cell12452 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12452 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12452 ⟨16,by decide⟩).lower ∧ (cell12452 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12452 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12452 ⟨17,by decide⟩).lower ∧ (cell12452 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12452 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12452 ⟨18,by decide⟩).lower ∧ (cell12452 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12452 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12452 ⟨19,by decide⟩).lower ∧ (cell12452 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12452 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12452 ⟨20,by decide⟩).lower ∧ (cell12452 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12452 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12452 ⟨21,by decide⟩).lower ∧ (cell12452 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12452 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12452 ⟨22,by decide⟩).lower ∧ (cell12452 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12452 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12452 ⟨23,by decide⟩).lower ∧ (cell12452 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12452 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12452 ⟨24,by decide⟩).lower ∧ (cell12452 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12452 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12452 ⟨25,by decide⟩).lower ∧ (cell12452 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12452 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12452 ⟨26,by decide⟩).lower ∧ (cell12452 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12452 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12452 ⟨27,by decide⟩).lower ∧ (cell12452 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12452 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12452 ⟨28,by decide⟩).lower ∧ (cell12452 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12452 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12452 ⟨29,by decide⟩).lower ∧ (cell12452 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12452 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12452 ⟨30,by decide⟩).lower ∧ (cell12452 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12452 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12452 ⟨31,by decide⟩).lower ∧ (cell12452 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12452 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12452 ⟨32,by decide⟩).lower ∧ (cell12452 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12452 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12452 ⟨33,by decide⟩).lower ∧ (cell12452 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12452 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12452 ⟨34,by decide⟩).lower ∧ (cell12452 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12452 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12452 ⟨35,by decide⟩).lower ∧ (cell12452 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12452 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12452 ⟨36,by decide⟩).lower ∧ (cell12452 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12452 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12452 ⟨37,by decide⟩).lower ∧ (cell12452 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12452 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12452 ⟨38,by decide⟩).lower ∧ (cell12452 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12452 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12452 ⟨39,by decide⟩).lower ∧ (cell12452 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12452 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12452 ⟨40,by decide⟩).lower ∧ (cell12452 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12452 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12452 ⟨41,by decide⟩).lower ∧ (cell12452 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12452 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12452 ⟨42,by decide⟩).lower ∧ (cell12452 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12452 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12452 ⟨43,by decide⟩).lower ∧ (cell12452 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12452 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12452 ⟨44,by decide⟩).lower ∧ (cell12452 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12452 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12452 ⟨45,by decide⟩).lower ∧ (cell12452 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12452 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12452 ⟨46,by decide⟩).lower ∧ (cell12452 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12452 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12452 ⟨47,by decide⟩).lower ∧ (cell12452 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12452 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12452 ⟨48,by decide⟩).lower ∧ (cell12452 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12452 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12452 ⟨49,by decide⟩).lower ∧ (cell12452 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12452 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12452 ⟨50,by decide⟩).lower ∧ (cell12452 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12452 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12452 ⟨51,by decide⟩).lower ∧ (cell12452 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12452 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12452 ⟨52,by decide⟩).lower ∧ (cell12452 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12452 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12452 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12452 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12452,cell12452,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12452 i).lower ∧
    (cell12452 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12452 i).upper ≤ (0.532 : ℝ) ∧
    (cell12452 i).centre ≤ (0.1 : ℝ) ∧ (cell12452 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12452 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12452 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12452

/-! The local source numeric instances at 12452 have no network premises. -/
namespace BstLean.Part269.N12452
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12452)
open BstLean.Part268 (cell12452)

noncomputable def sourceNumerics12452 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12452 (cell12452 i)
      scalarRow12452.M scalarRow12452.H scalarRow12452.xi := by
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
    energy_allowance := scalarRow12452.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12452]
    centre_nonneg := (scalarRow12452.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12452])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12452
/-! Actual 12453 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12453
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12453 ≤ (1.036165746578 : ℝ) := by
  have hr : (111.593010533814 : ℝ) ≤ √(12453 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.593010533814 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12453 12453 (11 / 1000) ≤
    (0.008565833088 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12453) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.593010533814 : ℝ) ≤ √(12453 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12453)
  have hdiv : K / √(12453 : ℝ) ≤ K / 111.593010533814 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.593010533814 ≤ (0.008565833088 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12453.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12453 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12453 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12453 := gPlus_lower 12453
end BstLean.Part269.N12453

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12453
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036165746577 : ℝ) ≤ wn 12453 := by
  have hn : √(12453 : ℝ) ≤ 111.593010533815 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12453 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.593010533815 ≤ 2 / √(12453 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256965237 : ℝ) ≤ rhoBar 12453 BstLean.Part154.csC ∧
    rhoBar 12453 BstLean.Part154.csC ≤ 0.000256965635 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036165746577 : ℝ) / (1.295212 * 12453) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036165746578 : ℝ) / (1.29521 * 12453) := by gcongr
      _ ≤ (0.000256965635 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12453 BstLean.Part154.csC) ≤ 0.001027928572 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12453 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12453 BstLean.Part154.csC) (piBar (rhoBar 12453 BstLean.Part154.csC)) ≤ 0.000196272270 ∧
    cc1 (rhoBar 12453 BstLean.Part154.csC) (piBar (rhoBar 12453 BstLean.Part154.csC)) ≤ 0.000124889311 ∧
    cc2 (rhoBar 12453 BstLean.Part154.csC) ≤ 0.000072499156 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12453 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12453 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12453 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12453 BstLean.Part154.csC * nuR (rhoBar 12453 BstLean.Part154.csC)) ≤ 0.000513947778 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256965635 : ℝ) * 0.001027928572 := by gcongr
      _ ≤ (0.000513947778 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12453 BstLean.Part154.csC) * nuR (rhoBar 12453 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001027928572 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12453 BstLean.Part154.csC) * rhoBar 12453 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256965635 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256965635 / 2 + 0.399 * 0.001027928572 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196272270 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513947778 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124889311 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256965635 / 1.414213562 := by gcongr
      _ ≤ (0.000072499156 : ℝ) := by norm_num

end BstLean.Part269.N12453

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12453
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12453 BstLean.Part154.csC) (piBar (rhoBar 12453 BstLean.Part154.csC)) ≤ 1.66362E-7 := by
  have hr0 : 0 ≤ rhoBar 12453 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12453 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12453 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12453 BstLean.Part154.csC) (piBar (rhoBar 12453 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12453 BstLean.Part154.csC) (piBar (rhoBar 12453 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12453 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196272270 : ℝ) ^ 2 + 0.000124889311 ^ 2 + 3 * 0.000072499156 ^ 2 +
        2 * 0.797885 * 0.000196272270 * 0.000124889311 + 2 * 0.000196272270 * 0.000072499156 +
        4 * 0.797885 * 0.000124889311 * 0.000072499156 := by gcongr
    _ ≤ (1.66362E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12453 BstLean.Part154.csC Θ ≤ 0.002683298457 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12453 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12453 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12453 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12453 BstLean.Part154.csC) (piBar (rhoBar 12453 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12453 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036165746578 * 1.66362E-7 / (0.000256965237 : ℝ) := by gcongr
    _ ≤ 0.002683298457 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12453 BstLean.Part154.csC Θ ≤ 0.002978279228 + 0.000678023090 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12453 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12453 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12453 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036165746578 : ℝ) * ((2 * Θ * 0.000256965635 +
        (6863 / 10000) * 0.000256965635 * 12453 * 0.001027928572) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002978279228 + 0.000678023090 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12453 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12453 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12453 0.011 Θ ∧ gammaRatio 12453 0.011 Θ ≤ 0.000088338140 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12453 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036165746578 : ℝ) * 0.525 / ((1 - 0.011) * 12453) := by gcongr
      _ ≤ (0.000088338140 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12453 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12453 0.011 Θ) :=
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
    badAllowance 12453 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12453 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12453 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12453 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12453 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12453 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12453 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12453 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12453 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12453 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12453 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036165746578 : ℝ) * 12453 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12453 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003794653974 + 0.003361321547 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12453

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12453
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12453 BstLean.Part154.csC) (piBar (rhoBar 12453 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12453 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12453 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12453 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12453 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12453 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12453 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12453 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12453 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12453 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12453 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12453 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12453 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12453 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12453 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053007930952 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12453) ≤ 0.010701723839 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12453 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036165746578)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010701723839 + 2 * 0.737676 / 12453) := by gcongr
    _ ≤ (0.053007930952 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12453 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12453

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12453
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492176664 : ℝ) ≤ plow 12453 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12453) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053065947787)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408731690) : eMP 12453 0.011 xi bn ≤ 0.001212438919 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12453 : ℝ) * (1 - 0.011))) ≤ 0.000599451378 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001408731690 / (12453 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599451378 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599451378 : ℝ) + 3.141593 * 0.053065947787 / (12453 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001212438919 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053065947787)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408731690) : PiBarMP 12453 12 0.011 xi bn ≤ 0.162858804667 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12453 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037533074615 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.977551784133 : ℝ) ≤ √((12453 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.593010533814 : ℝ) ≤ √(12453 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12453) ≤ 0.124850187267 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037533074615 + 0.053065947787 * 1.772454 / (2 * (110.977551784133 : ℝ))) * (1 + 0.001212438919) +
        8 / (12453 * 111.593010533814) + 0.124850187267 := by gcongr
    _ ≤ (0.162858804667 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053065947787)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408731690) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283368404530) :
    parallelOracle 12453 0.011 xi bn cd ≤ 0.163869617923 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12453 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12453 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492176664 : ℝ) ≤ plow 12453 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.593010533814 : ℝ) ≤ √(12453 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283368404530 : ℝ) / (2 * 0.560492176664 * 111.593010533814)) * 0.162858804667 +
        0.283368404530 ^ 2 / (2 * 0.560492176664 * 111.593010533814) := by gcongr
    _ ≤ (0.163869617923 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053065947787) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408731690)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283368404530) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12453 12453 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492176664 : ℝ) ≤ plow 12453 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.593010533814 : ℝ) ≤ √(12453 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12453 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12453 Θ 1.22 ≤ 0.011883365219 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.593010533814 := by gcongr <;> linarith
      _ ≤ (0.011883365219 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12453 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12453 12453 0.011 ≤ 0.008565833088 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12453 12453 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12453 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12453 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12453 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12453 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163869617923 + 0.011883365219 + (0.008565833088 : ℝ) *
        (1 + 2 * (0.283368404530 + 0.011883365219) / (0.560492176664 * 111.593010533814))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12453]

end BstLean.Part269.N12453

/-! The original eight local profiles supply actual 12453 moment certificates. -/
namespace BstLean.Part269.N12453
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12453 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12453 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12453 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053065947787 ∧
    0 ≤ bN 12453 BstLean.Part154.csC (groupTheta g) ∧ bN 12453 BstLean.Part154.csC (groupTheta g) ≤ 0.001408731690 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12453 12453 0.011
      (momentAllowance 12453 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12453 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12453 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12453 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12453 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12453 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230360473578 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12453 0.011
      (momentAllowance 12453 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12453 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12453
/-! The actual computed-centre upper energy formula at 12453. -/
namespace BstLean.Part269.N12453
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12453

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12453
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12453)
open BstLean.Part268 (cell12453)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086246638624
  | 2 => 0.087204136884
  | 3 => 0.088162060767
  | 4 => 0.089122344493
  | 5 => 0.090087308745
  | 6 => 0.091059715563
  | 7 => 0.092042827941
  | 8 => 0.093040474118
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12453 12453 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12453 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12453

/-! Actual upper energy certificates on all 43 source endpoints at 12453. -/
namespace BstLean.Part269.N12453
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12453)
open BstLean.Part268 (cell12453)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12453 (gMinus 12453) (1 - (cell12453 i).lower) ≤ 1 ∧
    energyUpper 12453 (gMinus 12453) (BstLean.Part211.gPlus 12453)
      (finiteEnergy 12453 12453 0.011) (1 - (cell12453 i).lower) ≤
      (cell12453 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨10,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨11,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨12,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨13,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨14,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨15,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨16,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨17,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨18,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨19,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨20,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨21,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨22,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨23,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨24,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨25,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨26,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨27,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨28,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨29,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨30,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨31,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨32,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨33,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨34,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨35,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨36,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨37,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨38,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨39,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨40,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨41,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨42,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨43,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨44,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨45,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨46,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨47,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨48,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨49,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨50,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨51,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12453) (by norm_num)
        (q := 1 - (cell12453 ⟨52,by decide⟩).lower)
        (by norm_num [cell12453]) (by norm_num [cell12453])
      exact ⟨E.1,E.2.trans (by norm_num [cell12453])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12453

/-! Source-cell containment and simple scalar guards at 12453. -/
namespace BstLean.Part269.N12453
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12453)
open BstLean.Part268 (cell12453)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12453 ⟨10,by decide⟩).lower ∧ (cell12453 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12453 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12453 ⟨11,by decide⟩).lower ∧ (cell12453 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12453 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12453 ⟨12,by decide⟩).lower ∧ (cell12453 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12453 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12453 ⟨13,by decide⟩).lower ∧ (cell12453 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12453 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12453 ⟨14,by decide⟩).lower ∧ (cell12453 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12453 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12453 ⟨15,by decide⟩).lower ∧ (cell12453 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12453 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12453 ⟨16,by decide⟩).lower ∧ (cell12453 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12453 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12453 ⟨17,by decide⟩).lower ∧ (cell12453 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12453 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12453 ⟨18,by decide⟩).lower ∧ (cell12453 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12453 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12453 ⟨19,by decide⟩).lower ∧ (cell12453 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12453 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12453 ⟨20,by decide⟩).lower ∧ (cell12453 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12453 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12453 ⟨21,by decide⟩).lower ∧ (cell12453 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12453 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12453 ⟨22,by decide⟩).lower ∧ (cell12453 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12453 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12453 ⟨23,by decide⟩).lower ∧ (cell12453 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12453 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12453 ⟨24,by decide⟩).lower ∧ (cell12453 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12453 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12453 ⟨25,by decide⟩).lower ∧ (cell12453 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12453 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12453 ⟨26,by decide⟩).lower ∧ (cell12453 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12453 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12453 ⟨27,by decide⟩).lower ∧ (cell12453 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12453 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12453 ⟨28,by decide⟩).lower ∧ (cell12453 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12453 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12453 ⟨29,by decide⟩).lower ∧ (cell12453 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12453 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12453 ⟨30,by decide⟩).lower ∧ (cell12453 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12453 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12453 ⟨31,by decide⟩).lower ∧ (cell12453 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12453 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12453 ⟨32,by decide⟩).lower ∧ (cell12453 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12453 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12453 ⟨33,by decide⟩).lower ∧ (cell12453 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12453 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12453 ⟨34,by decide⟩).lower ∧ (cell12453 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12453 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12453 ⟨35,by decide⟩).lower ∧ (cell12453 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12453 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12453 ⟨36,by decide⟩).lower ∧ (cell12453 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12453 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12453 ⟨37,by decide⟩).lower ∧ (cell12453 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12453 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12453 ⟨38,by decide⟩).lower ∧ (cell12453 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12453 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12453 ⟨39,by decide⟩).lower ∧ (cell12453 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12453 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12453 ⟨40,by decide⟩).lower ∧ (cell12453 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12453 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12453 ⟨41,by decide⟩).lower ∧ (cell12453 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12453 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12453 ⟨42,by decide⟩).lower ∧ (cell12453 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12453 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12453 ⟨43,by decide⟩).lower ∧ (cell12453 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12453 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12453 ⟨44,by decide⟩).lower ∧ (cell12453 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12453 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12453 ⟨45,by decide⟩).lower ∧ (cell12453 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12453 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12453 ⟨46,by decide⟩).lower ∧ (cell12453 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12453 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12453 ⟨47,by decide⟩).lower ∧ (cell12453 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12453 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12453 ⟨48,by decide⟩).lower ∧ (cell12453 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12453 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12453 ⟨49,by decide⟩).lower ∧ (cell12453 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12453 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12453 ⟨50,by decide⟩).lower ∧ (cell12453 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12453 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12453 ⟨51,by decide⟩).lower ∧ (cell12453 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12453 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12453 ⟨52,by decide⟩).lower ∧ (cell12453 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12453 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12453 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12453 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12453,cell12453,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12453 i).lower ∧
    (cell12453 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12453 i).upper ≤ (0.532 : ℝ) ∧
    (cell12453 i).centre ≤ (0.1 : ℝ) ∧ (cell12453 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12453 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12453 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12453

/-! The local source numeric instances at 12453 have no network premises. -/
namespace BstLean.Part269.N12453
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12453)
open BstLean.Part268 (cell12453)

noncomputable def sourceNumerics12453 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12453 (cell12453 i)
      scalarRow12453.M scalarRow12453.H scalarRow12453.xi := by
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
    energy_allowance := scalarRow12453.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12453]
    centre_nonneg := (scalarRow12453.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12453])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12453
/-! Actual 12454 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12454
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12454 ≤ (1.036164281681 : ℝ) := by
  have hr : (111.597491011223 : ℝ) ≤ √(12454 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.597491011223 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12454 12454 (11 / 1000) ≤
    (0.008565489179 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12454) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.597491011223 : ℝ) ≤ √(12454 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12454)
  have hdiv : K / √(12454 : ℝ) ≤ K / 111.597491011223 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.597491011223 ≤ (0.008565489179 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12454.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12454 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12454 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12454 := gPlus_lower 12454
end BstLean.Part269.N12454

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12454
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036164281680 : ℝ) ≤ wn 12454 := by
  have hn : √(12454 : ℝ) ≤ 111.597491011224 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12454 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.597491011224 ≤ 2 / √(12454 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256944240 : ℝ) ≤ rhoBar 12454 BstLean.Part154.csC ∧
    rhoBar 12454 BstLean.Part154.csC ≤ 0.000256944638 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036164281680 : ℝ) / (1.295212 * 12454) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036164281681 : ℝ) / (1.29521 * 12454) := by gcongr
      _ ≤ (0.000256944638 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12454 BstLean.Part154.csC) ≤ 0.001027844573 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12454 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12454 BstLean.Part154.csC) (piBar (rhoBar 12454 BstLean.Part154.csC)) ≤ 0.000196256231 ∧
    cc1 (rhoBar 12454 BstLean.Part154.csC) (piBar (rhoBar 12454 BstLean.Part154.csC)) ≤ 0.000124879105 ∧
    cc2 (rhoBar 12454 BstLean.Part154.csC) ≤ 0.000072493232 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12454 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12454 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12454 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12454 BstLean.Part154.csC * nuR (rhoBar 12454 BstLean.Part154.csC)) ≤ 0.000513905781 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256944638 : ℝ) * 0.001027844573 := by gcongr
      _ ≤ (0.000513905781 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12454 BstLean.Part154.csC) * nuR (rhoBar 12454 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001027844573 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12454 BstLean.Part154.csC) * rhoBar 12454 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256944638 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256944638 / 2 + 0.399 * 0.001027844573 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196256231 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513905781 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124879105 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256944638 / 1.414213562 := by gcongr
      _ ≤ (0.000072493232 : ℝ) := by norm_num

end BstLean.Part269.N12454

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12454
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12454 BstLean.Part154.csC) (piBar (rhoBar 12454 BstLean.Part154.csC)) ≤ 1.66334E-7 := by
  have hr0 : 0 ≤ rhoBar 12454 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12454 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12454 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12454 BstLean.Part154.csC) (piBar (rhoBar 12454 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12454 BstLean.Part154.csC) (piBar (rhoBar 12454 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12454 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196256231 : ℝ) ^ 2 + 0.000124879105 ^ 2 + 3 * 0.000072493232 ^ 2 +
        2 * 0.797885 * 0.000196256231 * 0.000124879105 + 2 * 0.000196256231 * 0.000072493232 +
        4 * 0.797885 * 0.000124879105 * 0.000072493232 := by gcongr
    _ ≤ (1.66334E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12454 BstLean.Part154.csC Θ ≤ 0.002683062281 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12454 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12454 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12454 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12454 BstLean.Part154.csC) (piBar (rhoBar 12454 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12454 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036164281681 * 1.66334E-7 / (0.000256944240 : ℝ) := by gcongr
    _ ≤ 0.002683062281 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12454 BstLean.Part154.csC Θ ≤ 0.002978027425 + 0.000677966729 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12454 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12454 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12454 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036164281681 : ℝ) * ((2 * Θ * 0.000256944638 +
        (6863 / 10000) * 0.000256944638 * 12454 * 0.001027844573) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002978027425 + 0.000677966729 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12454 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12454 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12454 0.011 Θ ∧ gammaRatio 12454 0.011 Θ ≤ 0.000088330922 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12454 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036164281681 : ℝ) * 0.525 / ((1 - 0.011) * 12454) := by gcongr
      _ ≤ (0.000088330922 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12454 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12454 0.011 Θ) :=
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
    badAllowance 12454 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12454 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12454 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12454 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12454 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12454 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12454 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12454 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12454 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12454 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12454 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036164281681 : ℝ) * 12454 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12454 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003794402171 + 0.003361029010 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12454

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12454
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12454 BstLean.Part154.csC) (piBar (rhoBar 12454 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12454 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12454 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12454 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12454 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12454 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12454 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12454 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12454 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12454 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12454 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12454 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12454 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12454 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12454 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053005779458 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12454) ≤ 0.010701294180 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12454 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036164281681)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010701294180 + 2 * 0.737676 / 12454) := by gcongr
    _ ≤ (0.053005779458 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12454 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12454

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12454
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492223695 : ℝ) ≤ plow 12454 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12454) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053065542402)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408607698) : eMP 12454 0.011 xi bn ≤ 0.001212336835 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12454 : ℝ) * (1 - 0.011))) ≤ 0.000599400931 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001408607698 / (12454 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599400931 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599400931 : ℝ) + 3.141593 * 0.053065542402 / (12454 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001212336835 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053065542402)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408607698) : PiBarMP 12454 12 0.011 xi bn ≤ 0.162852113461 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12454 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037531422809 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.982007550773 : ℝ) ≤ √((12454 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.597491011223 : ℝ) ≤ √(12454 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12454) ≤ 0.124845174713 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037531422809 + 0.053065542402 * 1.772454 / (2 * (110.982007550773 : ℝ))) * (1 + 0.001212336835) +
        8 / (12454 * 111.597491011223) + 0.124845174713 := by gcongr
    _ ≤ (0.162852113461 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053065542402)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408607698) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283365373142) :
    parallelOracle 12454 0.011 xi bn cd ≤ 0.163862853214 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12454 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12454 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492223695 : ℝ) ≤ plow 12454 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.597491011223 : ℝ) ≤ √(12454 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283365373142 : ℝ) / (2 * 0.560492223695 * 111.597491011223)) * 0.162852113461 +
        0.283365373142 ^ 2 / (2 * 0.560492223695 * 111.597491011223) := by gcongr
    _ ≤ (0.163862853214 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053065542402) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408607698)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283365373142) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12454 12454 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492223695 : ℝ) ≤ plow 12454 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.597491011223 : ℝ) ≤ √(12454 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12454 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12454 Θ 1.22 ≤ 0.011882888119 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.597491011223 := by gcongr <;> linarith
      _ ≤ (0.011882888119 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12454 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12454 12454 0.011 ≤ 0.008565489179 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12454 12454 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12454 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12454 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12454 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12454 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163862853214 + 0.011882888119 + (0.008565489179 : ℝ) *
        (1 + 2 * (0.283365373142 + 0.011882888119) / (0.560492223695 * 111.597491011223))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12454]

end BstLean.Part269.N12454

/-! The original eight local profiles supply actual 12454 moment certificates. -/
namespace BstLean.Part269.N12454
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12454 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12454 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12454 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053065542402 ∧
    0 ≤ bN 12454 BstLean.Part154.csC (groupTheta g) ∧ bN 12454 BstLean.Part154.csC (groupTheta g) ≤ 0.001408607698 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12454 12454 0.011
      (momentAllowance 12454 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12454 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12454 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12454 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12454 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12454 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230359593684 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12454 0.011
      (momentAllowance 12454 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12454 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12454
/-! The actual computed-centre upper energy formula at 12454. -/
namespace BstLean.Part269.N12454
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12454

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12454
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12454)
open BstLean.Part268 (cell12454)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086243417933
  | 2 => 0.087200849682
  | 3 => 0.088158696207
  | 4 => 0.089118889323
  | 5 => 0.090083746900
  | 6 => 0.091056027704
  | 7 => 0.092038990956
  | 8 => 0.093036460557
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12454 12454 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12454 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12454

/-! Actual upper energy certificates on all 43 source endpoints at 12454. -/
namespace BstLean.Part269.N12454
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12454)
open BstLean.Part268 (cell12454)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12454 (gMinus 12454) (1 - (cell12454 i).lower) ≤ 1 ∧
    energyUpper 12454 (gMinus 12454) (BstLean.Part211.gPlus 12454)
      (finiteEnergy 12454 12454 0.011) (1 - (cell12454 i).lower) ≤
      (cell12454 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨10,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨11,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨12,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨13,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨14,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨15,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨16,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨17,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨18,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨19,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨20,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨21,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨22,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨23,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨24,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨25,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨26,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨27,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨28,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨29,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨30,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨31,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨32,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨33,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨34,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨35,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨36,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨37,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨38,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨39,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨40,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨41,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨42,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨43,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨44,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨45,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨46,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨47,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨48,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨49,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨50,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨51,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12454) (by norm_num)
        (q := 1 - (cell12454 ⟨52,by decide⟩).lower)
        (by norm_num [cell12454]) (by norm_num [cell12454])
      exact ⟨E.1,E.2.trans (by norm_num [cell12454])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12454

/-! Source-cell containment and simple scalar guards at 12454. -/
namespace BstLean.Part269.N12454
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12454)
open BstLean.Part268 (cell12454)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12454 ⟨10,by decide⟩).lower ∧ (cell12454 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12454 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12454 ⟨11,by decide⟩).lower ∧ (cell12454 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12454 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12454 ⟨12,by decide⟩).lower ∧ (cell12454 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12454 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12454 ⟨13,by decide⟩).lower ∧ (cell12454 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12454 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12454 ⟨14,by decide⟩).lower ∧ (cell12454 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12454 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12454 ⟨15,by decide⟩).lower ∧ (cell12454 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12454 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12454 ⟨16,by decide⟩).lower ∧ (cell12454 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12454 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12454 ⟨17,by decide⟩).lower ∧ (cell12454 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12454 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12454 ⟨18,by decide⟩).lower ∧ (cell12454 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12454 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12454 ⟨19,by decide⟩).lower ∧ (cell12454 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12454 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12454 ⟨20,by decide⟩).lower ∧ (cell12454 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12454 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12454 ⟨21,by decide⟩).lower ∧ (cell12454 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12454 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12454 ⟨22,by decide⟩).lower ∧ (cell12454 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12454 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12454 ⟨23,by decide⟩).lower ∧ (cell12454 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12454 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12454 ⟨24,by decide⟩).lower ∧ (cell12454 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12454 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12454 ⟨25,by decide⟩).lower ∧ (cell12454 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12454 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12454 ⟨26,by decide⟩).lower ∧ (cell12454 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12454 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12454 ⟨27,by decide⟩).lower ∧ (cell12454 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12454 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12454 ⟨28,by decide⟩).lower ∧ (cell12454 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12454 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12454 ⟨29,by decide⟩).lower ∧ (cell12454 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12454 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12454 ⟨30,by decide⟩).lower ∧ (cell12454 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12454 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12454 ⟨31,by decide⟩).lower ∧ (cell12454 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12454 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12454 ⟨32,by decide⟩).lower ∧ (cell12454 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12454 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12454 ⟨33,by decide⟩).lower ∧ (cell12454 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12454 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12454 ⟨34,by decide⟩).lower ∧ (cell12454 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12454 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12454 ⟨35,by decide⟩).lower ∧ (cell12454 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12454 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12454 ⟨36,by decide⟩).lower ∧ (cell12454 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12454 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12454 ⟨37,by decide⟩).lower ∧ (cell12454 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12454 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12454 ⟨38,by decide⟩).lower ∧ (cell12454 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12454 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12454 ⟨39,by decide⟩).lower ∧ (cell12454 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12454 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12454 ⟨40,by decide⟩).lower ∧ (cell12454 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12454 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12454 ⟨41,by decide⟩).lower ∧ (cell12454 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12454 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12454 ⟨42,by decide⟩).lower ∧ (cell12454 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12454 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12454 ⟨43,by decide⟩).lower ∧ (cell12454 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12454 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12454 ⟨44,by decide⟩).lower ∧ (cell12454 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12454 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12454 ⟨45,by decide⟩).lower ∧ (cell12454 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12454 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12454 ⟨46,by decide⟩).lower ∧ (cell12454 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12454 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12454 ⟨47,by decide⟩).lower ∧ (cell12454 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12454 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12454 ⟨48,by decide⟩).lower ∧ (cell12454 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12454 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12454 ⟨49,by decide⟩).lower ∧ (cell12454 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12454 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12454 ⟨50,by decide⟩).lower ∧ (cell12454 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12454 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12454 ⟨51,by decide⟩).lower ∧ (cell12454 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12454 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12454 ⟨52,by decide⟩).lower ∧ (cell12454 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12454 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12454 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12454 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12454,cell12454,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12454 i).lower ∧
    (cell12454 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12454 i).upper ≤ (0.532 : ℝ) ∧
    (cell12454 i).centre ≤ (0.1 : ℝ) ∧ (cell12454 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12454 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12454 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12454

/-! The local source numeric instances at 12454 have no network premises. -/
namespace BstLean.Part269.N12454
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12454)
open BstLean.Part268 (cell12454)

noncomputable def sourceNumerics12454 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12454 (cell12454 i)
      scalarRow12454.M scalarRow12454.H scalarRow12454.xi := by
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
    energy_allowance := scalarRow12454.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12454]
    centre_nonneg := (scalarRow12454.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12454])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12454
/-! Actual 12455 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12455
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12455 ≤ (1.036162816960 : ℝ) := by
  have hr : (111.601971308754 : ℝ) ≤ √(12455 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.601971308754 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12455 12455 (11 / 1000) ≤
    (0.008565145312 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12455) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.601971308754 : ℝ) ≤ √(12455 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12455)
  have hdiv : K / √(12455 : ℝ) ≤ K / 111.601971308754 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.601971308754 ≤ (0.008565145312 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12455.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12455 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12455 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12455 := gPlus_lower 12455
end BstLean.Part269.N12455

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12455
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036162816959 : ℝ) ≤ wn 12455 := by
  have hn : √(12455 : ℝ) ≤ 111.601971308755 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12455 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.601971308755 ≤ 2 / √(12455 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256923247 : ℝ) ≤ rhoBar 12455 BstLean.Part154.csC ∧
    rhoBar 12455 BstLean.Part154.csC ≤ 0.000256923645 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036162816959 : ℝ) / (1.295212 * 12455) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036162816960 : ℝ) / (1.29521 * 12455) := by gcongr
      _ ≤ (0.000256923645 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12455 BstLean.Part154.csC) ≤ 0.001027760590 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12455 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12455 BstLean.Part154.csC) (piBar (rhoBar 12455 BstLean.Part154.csC)) ≤ 0.000196240196 ∧
    cc1 (rhoBar 12455 BstLean.Part154.csC) (piBar (rhoBar 12455 BstLean.Part154.csC)) ≤ 0.000124868902 ∧
    cc2 (rhoBar 12455 BstLean.Part154.csC) ≤ 0.000072487309 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12455 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12455 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12455 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12455 BstLean.Part154.csC * nuR (rhoBar 12455 BstLean.Part154.csC)) ≤ 0.000513863793 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256923645 : ℝ) * 0.001027760590 := by gcongr
      _ ≤ (0.000513863793 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12455 BstLean.Part154.csC) * nuR (rhoBar 12455 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001027760590 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12455 BstLean.Part154.csC) * rhoBar 12455 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256923645 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256923645 / 2 + 0.399 * 0.001027760590 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196240196 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513863793 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124868902 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256923645 / 1.414213562 := by gcongr
      _ ≤ (0.000072487309 : ℝ) := by norm_num

end BstLean.Part269.N12455

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12455
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12455 BstLean.Part154.csC) (piBar (rhoBar 12455 BstLean.Part154.csC)) ≤ 1.66307E-7 := by
  have hr0 : 0 ≤ rhoBar 12455 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12455 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12455 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12455 BstLean.Part154.csC) (piBar (rhoBar 12455 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12455 BstLean.Part154.csC) (piBar (rhoBar 12455 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12455 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196240196 : ℝ) ^ 2 + 0.000124868902 ^ 2 + 3 * 0.000072487309 ^ 2 +
        2 * 0.797885 * 0.000196240196 * 0.000124868902 + 2 * 0.000196240196 * 0.000072487309 +
        4 * 0.797885 * 0.000124868902 * 0.000072487309 := by gcongr
    _ ≤ (1.66307E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12455 BstLean.Part154.csC Θ ≤ 0.002682842158 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12455 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12455 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12455 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12455 BstLean.Part154.csC) (piBar (rhoBar 12455 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12455 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036162816960 * 1.66307E-7 / (0.000256923247 : ℝ) := by gcongr
    _ ≤ 0.002682842158 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12455 BstLean.Part154.csC Θ ≤ 0.002977775679 + 0.000677910379 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12455 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12455 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12455 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036162816960 : ℝ) * ((2 * Θ * 0.000256923645 +
        (6863 / 10000) * 0.000256923645 * 12455 * 0.001027760590) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002977775679 + 0.000677910379 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12455 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12455 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12455 0.011 Θ ∧ gammaRatio 12455 0.011 Θ ≤ 0.000088323706 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12455 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036162816960 : ℝ) * 0.525 / ((1 - 0.011) * 12455) := by gcongr
      _ ≤ (0.000088323706 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12455 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12455 0.011 Θ) :=
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
    badAllowance 12455 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12455 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12455 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12455 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12455 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12455 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12455 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12455 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12455 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12455 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12455 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036162816960 : ℝ) * 12455 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12455 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003794150425 + 0.003360752537 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12455

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12455
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12455 BstLean.Part154.csC) (piBar (rhoBar 12455 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12455 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12455 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12455 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12455 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12455 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12455 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12455 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12455 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12455 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12455 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12455 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12455 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12455 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12455 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053003628226 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12455) ≤ 0.010700864573 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12455 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036162816960)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010700864573 + 2 * 0.737676 / 12455) := by gcongr
    _ ≤ (0.053003628226 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12455 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12455

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12455
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492270718 : ℝ) ≤ plow 12455 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12455) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053065145507)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408492133) : eMP 12455 0.011 xi bn ≤ 0.001212238345 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12455 : ℝ) * (1 - 0.011))) ≤ 0.000599352280 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001408492133 / (12455 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599352280 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599352280 : ℝ) + 3.141593 * 0.053065145507 / (12455 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001212238345 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053065145507)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408492133) : PiBarMP 12455 12 0.011 xi bn ≤ 0.162845535399 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12455 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037529883200 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.986463138528 : ℝ) ≤ √((12455 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.601971308754 : ℝ) ≤ √(12455 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12455) ≤ 0.124840162763 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037529883200 + 0.053065145507 * 1.772454 / (2 * (110.986463138528 : ℝ))) * (1 + 0.001212238345) +
        8 / (12455 * 111.601971308754) + 0.124840162763 := by gcongr
    _ ≤ (0.162845535399 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053065145507)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408492133) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283362360440) :
    parallelOracle 12455 0.011 xi bn cd ≤ 0.163856202021 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12455 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12455 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492270718 : ℝ) ≤ plow 12455 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.601971308754 : ℝ) ≤ √(12455 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283362360440 : ℝ) / (2 * 0.560492270718 * 111.601971308754)) * 0.162845535399 +
        0.283362360440 ^ 2 / (2 * 0.560492270718 * 111.601971308754) := by gcongr
    _ ≤ (0.163856202021 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053065145507) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408492133)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283362360440) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12455 12455 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492270718 : ℝ) ≤ plow 12455 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.601971308754 : ℝ) ≤ √(12455 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12455 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12455 Θ 1.22 ≤ 0.011882411077 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.601971308754 := by gcongr <;> linarith
      _ ≤ (0.011882411077 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12455 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12455 12455 0.011 ≤ 0.008565145312 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12455 12455 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12455 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12455 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12455 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12455 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163856202021 + 0.011882411077 + (0.008565145312 : ℝ) *
        (1 + 2 * (0.283362360440 + 0.011882411077) / (0.560492270718 * 111.601971308754))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12455]

end BstLean.Part269.N12455

/-! The original eight local profiles supply actual 12455 moment certificates. -/
namespace BstLean.Part269.N12455
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12455 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12455 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12455 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053065145507 ∧
    0 ≤ bN 12455 BstLean.Part154.csC (groupTheta g) ∧ bN 12455 BstLean.Part154.csC (groupTheta g) ≤ 0.001408492133 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12455 12455 0.011
      (momentAllowance 12455 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12455 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12455 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12455 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12455 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12455 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230358732214 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12455 0.011
      (momentAllowance 12455 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12455 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12455
/-! The actual computed-centre upper energy formula at 12455. -/
namespace BstLean.Part269.N12455
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12455

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12455
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12455)
open BstLean.Part268 (cell12455)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086240198644
  | 2 => 0.087197563943
  | 3 => 0.088155333186
  | 4 => 0.089115435786
  | 5 => 0.090080186799
  | 6 => 0.091052341728
  | 7 => 0.092035156018
  | 8 => 0.093032449242
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12455 12455 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12455 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12455

/-! Actual upper energy certificates on all 43 source endpoints at 12455. -/
namespace BstLean.Part269.N12455
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12455)
open BstLean.Part268 (cell12455)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12455 (gMinus 12455) (1 - (cell12455 i).lower) ≤ 1 ∧
    energyUpper 12455 (gMinus 12455) (BstLean.Part211.gPlus 12455)
      (finiteEnergy 12455 12455 0.011) (1 - (cell12455 i).lower) ≤
      (cell12455 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨10,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨11,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨12,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨13,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨14,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨15,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨16,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨17,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨18,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨19,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨20,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨21,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨22,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨23,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨24,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨25,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨26,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨27,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨28,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨29,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨30,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨31,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨32,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨33,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨34,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨35,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨36,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨37,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨38,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨39,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨40,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨41,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨42,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨43,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨44,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨45,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨46,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨47,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨48,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨49,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨50,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨51,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12455) (by norm_num)
        (q := 1 - (cell12455 ⟨52,by decide⟩).lower)
        (by norm_num [cell12455]) (by norm_num [cell12455])
      exact ⟨E.1,E.2.trans (by norm_num [cell12455])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12455

/-! Source-cell containment and simple scalar guards at 12455. -/
namespace BstLean.Part269.N12455
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12455)
open BstLean.Part268 (cell12455)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12455 ⟨10,by decide⟩).lower ∧ (cell12455 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12455 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12455 ⟨11,by decide⟩).lower ∧ (cell12455 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12455 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12455 ⟨12,by decide⟩).lower ∧ (cell12455 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12455 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12455 ⟨13,by decide⟩).lower ∧ (cell12455 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12455 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12455 ⟨14,by decide⟩).lower ∧ (cell12455 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12455 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12455 ⟨15,by decide⟩).lower ∧ (cell12455 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12455 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12455 ⟨16,by decide⟩).lower ∧ (cell12455 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12455 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12455 ⟨17,by decide⟩).lower ∧ (cell12455 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12455 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12455 ⟨18,by decide⟩).lower ∧ (cell12455 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12455 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12455 ⟨19,by decide⟩).lower ∧ (cell12455 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12455 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12455 ⟨20,by decide⟩).lower ∧ (cell12455 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12455 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12455 ⟨21,by decide⟩).lower ∧ (cell12455 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12455 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12455 ⟨22,by decide⟩).lower ∧ (cell12455 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12455 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12455 ⟨23,by decide⟩).lower ∧ (cell12455 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12455 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12455 ⟨24,by decide⟩).lower ∧ (cell12455 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12455 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12455 ⟨25,by decide⟩).lower ∧ (cell12455 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12455 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12455 ⟨26,by decide⟩).lower ∧ (cell12455 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12455 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12455 ⟨27,by decide⟩).lower ∧ (cell12455 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12455 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12455 ⟨28,by decide⟩).lower ∧ (cell12455 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12455 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12455 ⟨29,by decide⟩).lower ∧ (cell12455 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12455 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12455 ⟨30,by decide⟩).lower ∧ (cell12455 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12455 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12455 ⟨31,by decide⟩).lower ∧ (cell12455 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12455 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12455 ⟨32,by decide⟩).lower ∧ (cell12455 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12455 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12455 ⟨33,by decide⟩).lower ∧ (cell12455 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12455 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12455 ⟨34,by decide⟩).lower ∧ (cell12455 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12455 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12455 ⟨35,by decide⟩).lower ∧ (cell12455 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12455 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12455 ⟨36,by decide⟩).lower ∧ (cell12455 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12455 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12455 ⟨37,by decide⟩).lower ∧ (cell12455 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12455 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12455 ⟨38,by decide⟩).lower ∧ (cell12455 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12455 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12455 ⟨39,by decide⟩).lower ∧ (cell12455 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12455 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12455 ⟨40,by decide⟩).lower ∧ (cell12455 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12455 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12455 ⟨41,by decide⟩).lower ∧ (cell12455 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12455 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12455 ⟨42,by decide⟩).lower ∧ (cell12455 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12455 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12455 ⟨43,by decide⟩).lower ∧ (cell12455 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12455 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12455 ⟨44,by decide⟩).lower ∧ (cell12455 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12455 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12455 ⟨45,by decide⟩).lower ∧ (cell12455 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12455 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12455 ⟨46,by decide⟩).lower ∧ (cell12455 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12455 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12455 ⟨47,by decide⟩).lower ∧ (cell12455 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12455 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12455 ⟨48,by decide⟩).lower ∧ (cell12455 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12455 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12455 ⟨49,by decide⟩).lower ∧ (cell12455 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12455 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12455 ⟨50,by decide⟩).lower ∧ (cell12455 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12455 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12455 ⟨51,by decide⟩).lower ∧ (cell12455 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12455 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12455 ⟨52,by decide⟩).lower ∧ (cell12455 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12455 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12455 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12455 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12455,cell12455,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12455 i).lower ∧
    (cell12455 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12455 i).upper ≤ (0.532 : ℝ) ∧
    (cell12455 i).centre ≤ (0.1 : ℝ) ∧ (cell12455 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12455 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12455 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12455

/-! The local source numeric instances at 12455 have no network premises. -/
namespace BstLean.Part269.N12455
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12455)
open BstLean.Part268 (cell12455)

noncomputable def sourceNumerics12455 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12455 (cell12455 i)
      scalarRow12455.M scalarRow12455.H scalarRow12455.xi := by
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
    energy_allowance := scalarRow12455.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12455]
    centre_nonneg := (scalarRow12455.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12455])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12455
/-! Actual 12456 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12456
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12456 ≤ (1.036161352417 : ℝ) := by
  have hr : (111.606451426429 : ℝ) ≤ √(12456 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.606451426429 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12456 12456 (11 / 1000) ≤
    (0.008564801487 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12456) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.606451426429 : ℝ) ≤ √(12456 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12456)
  have hdiv : K / √(12456 : ℝ) ≤ K / 111.606451426429 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.606451426429 ≤ (0.008564801487 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12456.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12456 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12456 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12456 := gPlus_lower 12456
end BstLean.Part269.N12456

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12456
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036161352416 : ℝ) ≤ wn 12456 := by
  have hn : √(12456 : ℝ) ≤ 111.606451426430 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12456 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.606451426430 ≤ 2 / √(12456 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256902258 : ℝ) ≤ rhoBar 12456 BstLean.Part154.csC ∧
    rhoBar 12456 BstLean.Part154.csC ≤ 0.000256902655 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036161352416 : ℝ) / (1.295212 * 12456) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036161352417 : ℝ) / (1.29521 * 12456) := by gcongr
      _ ≤ (0.000256902655 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12456 BstLean.Part154.csC) ≤ 0.001027676619 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12456 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12456 BstLean.Part154.csC) (piBar (rhoBar 12456 BstLean.Part154.csC)) ≤ 0.000196224163 ∧
    cc1 (rhoBar 12456 BstLean.Part154.csC) (piBar (rhoBar 12456 BstLean.Part154.csC)) ≤ 0.000124858700 ∧
    cc2 (rhoBar 12456 BstLean.Part154.csC) ≤ 0.000072481387 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12456 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12456 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12456 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12456 BstLean.Part154.csC * nuR (rhoBar 12456 BstLean.Part154.csC)) ≤ 0.000513821810 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256902655 : ℝ) * 0.001027676619 := by gcongr
      _ ≤ (0.000513821810 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12456 BstLean.Part154.csC) * nuR (rhoBar 12456 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001027676619 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12456 BstLean.Part154.csC) * rhoBar 12456 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256902655 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256902655 / 2 + 0.399 * 0.001027676619 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196224163 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513821810 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124858700 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256902655 / 1.414213562 := by gcongr
      _ ≤ (0.000072481387 : ℝ) := by norm_num

end BstLean.Part269.N12456

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12456
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12456 BstLean.Part154.csC) (piBar (rhoBar 12456 BstLean.Part154.csC)) ≤ 1.66280E-7 := by
  have hr0 : 0 ≤ rhoBar 12456 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12456 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12456 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12456 BstLean.Part154.csC) (piBar (rhoBar 12456 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12456 BstLean.Part154.csC) (piBar (rhoBar 12456 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12456 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196224163 : ℝ) ^ 2 + 0.000124858700 ^ 2 + 3 * 0.000072481387 ^ 2 +
        2 * 0.797885 * 0.000196224163 * 0.000124858700 + 2 * 0.000196224163 * 0.000072481387 +
        4 * 0.797885 * 0.000124858700 * 0.000072481387 := by gcongr
    _ ≤ (1.66280E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12456 BstLean.Part154.csC Θ ≤ 0.002682621960 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12456 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12456 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12456 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12456 BstLean.Part154.csC) (piBar (rhoBar 12456 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12456 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036161352417 * 1.66280E-7 / (0.000256902258 : ℝ) := by gcongr
    _ ≤ 0.002682621960 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12456 BstLean.Part154.csC Θ ≤ 0.002977523964 + 0.000677854037 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12456 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12456 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12456 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036161352417 : ℝ) * ((2 * Θ * 0.000256902655 +
        (6863 / 10000) * 0.000256902655 * 12456 * 0.001027676619) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002977523964 + 0.000677854037 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12456 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12456 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12456 0.011 Θ ∧ gammaRatio 12456 0.011 Θ ≤ 0.000088316490 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12456 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036161352417 : ℝ) * 0.525 / ((1 - 0.011) * 12456) := by gcongr
      _ ≤ (0.000088316490 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12456 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12456 0.011 Θ) :=
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
    badAllowance 12456 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12456 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12456 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12456 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12456 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12456 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12456 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12456 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12456 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12456 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12456 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036161352417 : ℝ) * 12456 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12456 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003793898710 + 0.003360475997 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12456

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12456
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12456 BstLean.Part154.csC) (piBar (rhoBar 12456 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12456 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12456 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12456 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12456 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12456 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12456 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12456 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12456 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12456 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12456 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12456 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12456 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12456 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12456 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053001477256 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12456) ≤ 0.010700435018 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12456 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036161352417)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010700435018 + 2 * 0.737676 / 12456) := by gcongr
    _ ≤ (0.053001477256 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12456 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12456

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12456
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492317734 : ℝ) ≤ plow 12456 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12456) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053064748609)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408376529) : eMP 12456 0.011 xi bn ≤ 0.001212139847 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12456 : ℝ) * (1 - 0.011))) ≤ 0.000599303625 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001408376529 / (12456 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599303625 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599303625 : ℝ) + 3.141593 * 0.053064748609 / (12456 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001212139847 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053064748609)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408376529) : PiBarMP 12456 12 0.011 xi bn ≤ 0.162838957360 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12456 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037528343009 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.990918547419 : ℝ) ≤ √((12456 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.606451426429 : ℝ) ≤ √(12456 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12456) ≤ 0.124835151416 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037528343009 + 0.053064748609 * 1.772454 / (2 * (110.990918547419 : ℝ))) * (1 + 0.001212139847) +
        8 / (12456 * 111.606451426429) + 0.124835151416 := by gcongr
    _ ≤ (0.162838957360 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053064748609)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408376529) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283359347990) :
    parallelOracle 12456 0.011 xi bn cd ≤ 0.163849550862 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12456 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12456 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492317734 : ℝ) ≤ plow 12456 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.606451426429 : ℝ) ≤ √(12456 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283359347990 : ℝ) / (2 * 0.560492317734 * 111.606451426429)) * 0.162838957360 +
        0.283359347990 ^ 2 / (2 * 0.560492317734 * 111.606451426429) := by gcongr
    _ ≤ (0.163849550862 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053064748609) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408376529)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283359347990) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12456 12456 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492317734 : ℝ) ≤ plow 12456 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.606451426429 : ℝ) ≤ √(12456 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12456 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12456 Θ 1.22 ≤ 0.011881934092 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.606451426429 := by gcongr <;> linarith
      _ ≤ (0.011881934092 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12456 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12456 12456 0.011 ≤ 0.008564801487 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12456 12456 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12456 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12456 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12456 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12456 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163849550862 + 0.011881934092 + (0.008564801487 : ℝ) *
        (1 + 2 * (0.283359347990 + 0.011881934092) / (0.560492317734 * 111.606451426429))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12456]

end BstLean.Part269.N12456

/-! The original eight local profiles supply actual 12456 moment certificates. -/
namespace BstLean.Part269.N12456
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12456 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12456 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12456 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053064748609 ∧
    0 ≤ bN 12456 BstLean.Part154.csC (groupTheta g) ∧ bN 12456 BstLean.Part154.csC (groupTheta g) ≤ 0.001408376529 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12456 12456 0.011
      (momentAllowance 12456 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12456 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12456 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12456 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12456 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12456 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230357870734 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12456 0.011
      (momentAllowance 12456 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12456 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12456
/-! The actual computed-centre upper energy formula at 12456. -/
namespace BstLean.Part269.N12456
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12456

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12456
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12456)
open BstLean.Part268 (cell12456)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086236980756
  | 2 => 0.087194279666
  | 3 => 0.088151971703
  | 4 => 0.089111983878
  | 5 => 0.090076628441
  | 6 => 0.091048657631
  | 7 => 0.092031323125
  | 8 => 0.093028440170
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12456 12456 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12456 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12456

/-! Actual upper energy certificates on all 43 source endpoints at 12456. -/
namespace BstLean.Part269.N12456
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12456)
open BstLean.Part268 (cell12456)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12456 (gMinus 12456) (1 - (cell12456 i).lower) ≤ 1 ∧
    energyUpper 12456 (gMinus 12456) (BstLean.Part211.gPlus 12456)
      (finiteEnergy 12456 12456 0.011) (1 - (cell12456 i).lower) ≤
      (cell12456 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨10,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨11,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨12,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨13,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨14,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨15,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨16,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨17,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨18,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨19,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨20,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨21,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨22,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨23,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨24,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨25,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨26,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨27,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨28,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨29,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨30,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨31,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨32,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨33,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨34,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨35,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨36,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨37,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨38,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨39,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨40,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨41,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨42,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨43,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨44,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨45,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨46,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨47,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨48,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨49,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨50,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨51,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12456) (by norm_num)
        (q := 1 - (cell12456 ⟨52,by decide⟩).lower)
        (by norm_num [cell12456]) (by norm_num [cell12456])
      exact ⟨E.1,E.2.trans (by norm_num [cell12456])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12456

/-! Source-cell containment and simple scalar guards at 12456. -/
namespace BstLean.Part269.N12456
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12456)
open BstLean.Part268 (cell12456)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12456 ⟨10,by decide⟩).lower ∧ (cell12456 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12456 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12456 ⟨11,by decide⟩).lower ∧ (cell12456 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12456 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12456 ⟨12,by decide⟩).lower ∧ (cell12456 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12456 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12456 ⟨13,by decide⟩).lower ∧ (cell12456 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12456 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12456 ⟨14,by decide⟩).lower ∧ (cell12456 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12456 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12456 ⟨15,by decide⟩).lower ∧ (cell12456 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12456 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12456 ⟨16,by decide⟩).lower ∧ (cell12456 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12456 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12456 ⟨17,by decide⟩).lower ∧ (cell12456 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12456 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12456 ⟨18,by decide⟩).lower ∧ (cell12456 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12456 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12456 ⟨19,by decide⟩).lower ∧ (cell12456 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12456 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12456 ⟨20,by decide⟩).lower ∧ (cell12456 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12456 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12456 ⟨21,by decide⟩).lower ∧ (cell12456 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12456 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12456 ⟨22,by decide⟩).lower ∧ (cell12456 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12456 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12456 ⟨23,by decide⟩).lower ∧ (cell12456 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12456 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12456 ⟨24,by decide⟩).lower ∧ (cell12456 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12456 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12456 ⟨25,by decide⟩).lower ∧ (cell12456 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12456 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12456 ⟨26,by decide⟩).lower ∧ (cell12456 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12456 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12456 ⟨27,by decide⟩).lower ∧ (cell12456 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12456 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12456 ⟨28,by decide⟩).lower ∧ (cell12456 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12456 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12456 ⟨29,by decide⟩).lower ∧ (cell12456 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12456 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12456 ⟨30,by decide⟩).lower ∧ (cell12456 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12456 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12456 ⟨31,by decide⟩).lower ∧ (cell12456 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12456 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12456 ⟨32,by decide⟩).lower ∧ (cell12456 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12456 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12456 ⟨33,by decide⟩).lower ∧ (cell12456 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12456 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12456 ⟨34,by decide⟩).lower ∧ (cell12456 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12456 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12456 ⟨35,by decide⟩).lower ∧ (cell12456 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12456 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12456 ⟨36,by decide⟩).lower ∧ (cell12456 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12456 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12456 ⟨37,by decide⟩).lower ∧ (cell12456 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12456 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12456 ⟨38,by decide⟩).lower ∧ (cell12456 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12456 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12456 ⟨39,by decide⟩).lower ∧ (cell12456 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12456 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12456 ⟨40,by decide⟩).lower ∧ (cell12456 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12456 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12456 ⟨41,by decide⟩).lower ∧ (cell12456 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12456 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12456 ⟨42,by decide⟩).lower ∧ (cell12456 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12456 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12456 ⟨43,by decide⟩).lower ∧ (cell12456 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12456 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12456 ⟨44,by decide⟩).lower ∧ (cell12456 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12456 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12456 ⟨45,by decide⟩).lower ∧ (cell12456 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12456 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12456 ⟨46,by decide⟩).lower ∧ (cell12456 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12456 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12456 ⟨47,by decide⟩).lower ∧ (cell12456 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12456 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12456 ⟨48,by decide⟩).lower ∧ (cell12456 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12456 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12456 ⟨49,by decide⟩).lower ∧ (cell12456 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12456 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12456 ⟨50,by decide⟩).lower ∧ (cell12456 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12456 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12456 ⟨51,by decide⟩).lower ∧ (cell12456 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12456 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12456 ⟨52,by decide⟩).lower ∧ (cell12456 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12456 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12456 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12456 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12456,cell12456,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12456 i).lower ∧
    (cell12456 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12456 i).upper ≤ (0.532 : ℝ) ∧
    (cell12456 i).centre ≤ (0.1 : ℝ) ∧ (cell12456 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12456 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12456 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12456

/-! The local source numeric instances at 12456 have no network premises. -/
namespace BstLean.Part269.N12456
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12456)
open BstLean.Part268 (cell12456)

noncomputable def sourceNumerics12456 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12456 (cell12456 i)
      scalarRow12456.M scalarRow12456.H scalarRow12456.xi := by
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
    energy_allowance := scalarRow12456.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12456]
    centre_nonneg := (scalarRow12456.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12456])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12456
/-! Actual 12457 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12457
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12457 ≤ (1.036159888052 : ℝ) := by
  have hr : (111.610931364270 : ℝ) ≤ √(12457 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.610931364270 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12457 12457 (11 / 1000) ≤
    (0.008564457703 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12457) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.610931364270 : ℝ) ≤ √(12457 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12457)
  have hdiv : K / √(12457 : ℝ) ≤ K / 111.610931364270 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.610931364270 ≤ (0.008564457703 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12457.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12457 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12457 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12457 := gPlus_lower 12457
end BstLean.Part269.N12457

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12457
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036159888051 : ℝ) ≤ wn 12457 := by
  have hn : √(12457 : ℝ) ≤ 111.610931364271 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12457 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.610931364271 ≤ 2 / √(12457 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256881272 : ℝ) ≤ rhoBar 12457 BstLean.Part154.csC ∧
    rhoBar 12457 BstLean.Part154.csC ≤ 0.000256881669 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036159888051 : ℝ) / (1.295212 * 12457) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036159888052 : ℝ) / (1.29521 * 12457) := by gcongr
      _ ≤ (0.000256881669 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12457 BstLean.Part154.csC) ≤ 0.001027592665 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12457 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12457 BstLean.Part154.csC) (piBar (rhoBar 12457 BstLean.Part154.csC)) ≤ 0.000196208133 ∧
    cc1 (rhoBar 12457 BstLean.Part154.csC) (piBar (rhoBar 12457 BstLean.Part154.csC)) ≤ 0.000124848500 ∧
    cc2 (rhoBar 12457 BstLean.Part154.csC) ≤ 0.000072475466 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12457 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12457 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12457 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12457 BstLean.Part154.csC * nuR (rhoBar 12457 BstLean.Part154.csC)) ≤ 0.000513779835 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256881669 : ℝ) * 0.001027592665 := by gcongr
      _ ≤ (0.000513779835 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12457 BstLean.Part154.csC) * nuR (rhoBar 12457 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001027592665 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12457 BstLean.Part154.csC) * rhoBar 12457 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256881669 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256881669 / 2 + 0.399 * 0.001027592665 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196208133 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513779835 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124848500 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256881669 / 1.414213562 := by gcongr
      _ ≤ (0.000072475466 : ℝ) := by norm_num

end BstLean.Part269.N12457

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12457
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12457 BstLean.Part154.csC) (piBar (rhoBar 12457 BstLean.Part154.csC)) ≤ 1.66253E-7 := by
  have hr0 : 0 ≤ rhoBar 12457 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12457 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12457 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12457 BstLean.Part154.csC) (piBar (rhoBar 12457 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12457 BstLean.Part154.csC) (piBar (rhoBar 12457 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12457 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196208133 : ℝ) ^ 2 + 0.000124848500 ^ 2 + 3 * 0.000072475466 ^ 2 +
        2 * 0.797885 * 0.000196208133 * 0.000124848500 + 2 * 0.000196208133 * 0.000072475466 +
        4 * 0.797885 * 0.000124848500 * 0.000072475466 := by gcongr
    _ ≤ (1.66253E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12457 BstLean.Part154.csC Θ ≤ 0.002682401696 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12457 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12457 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12457 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12457 BstLean.Part154.csC) (piBar (rhoBar 12457 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12457 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036159888052 * 1.66253E-7 / (0.000256881272 : ℝ) := by gcongr
    _ ≤ 0.002682401696 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12457 BstLean.Part154.csC Θ ≤ 0.002977272308 + 0.000677797707 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12457 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12457 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12457 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036159888052 : ℝ) * ((2 * Θ * 0.000256881669 +
        (6863 / 10000) * 0.000256881669 * 12457 * 0.001027592665) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002977272308 + 0.000677797707 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12457 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12457 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12457 0.011 Θ ∧ gammaRatio 12457 0.011 Θ ≤ 0.000088309275 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12457 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036159888052 : ℝ) * 0.525 / ((1 - 0.011) * 12457) := by gcongr
      _ ≤ (0.000088309275 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12457 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12457 0.011 Θ) :=
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
    badAllowance 12457 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12457 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12457 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12457 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12457 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12457 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12457 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12457 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12457 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12457 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12457 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036159888052 : ℝ) * 12457 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12457 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003793647054 + 0.003360199403 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12457

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12457
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12457 BstLean.Part154.csC) (piBar (rhoBar 12457 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12457 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12457 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12457 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12457 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12457 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12457 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12457 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12457 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12457 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12457 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12457 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12457 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12457 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12457 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052999326548 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12457) ≤ 0.010700005515 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12457 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036159888052)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010700005515 + 2 * 0.737676 / 12457) := by gcongr
    _ ≤ (0.052999326548 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12457 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12457

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12457
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492364742 : ℝ) ≤ plow 12457 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12457) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053064351741)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408260891) : eMP 12457 0.011 xi bn ≤ 0.001212041342 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12457 : ℝ) * (1 - 0.011))) ≤ 0.000599254966 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001408260891 / (12457 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599254966 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599254966 : ℝ) + 3.141593 * 0.053064351741 / (12457 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001212041342 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053064351741)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408260891) : PiBarMP 12457 12 0.011 xi bn ≤ 0.162832379411 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12457 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037526802302 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.995373777468 : ℝ) ≤ √((12457 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.610931364270 : ℝ) ≤ √(12457 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12457) ≤ 0.124830140673 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037526802302 + 0.053064351741 * 1.772454 / (2 * (110.995373777468 : ℝ))) * (1 + 0.001212041342) +
        8 / (12457 * 111.610931364270) + 0.124830140673 := by gcongr
    _ ≤ (0.162832379411 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053064351741)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408260891) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283356335864) :
    parallelOracle 12457 0.011 xi bn cd ≤ 0.163842899802 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12457 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12457 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492364742 : ℝ) ≤ plow 12457 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.610931364270 : ℝ) ≤ √(12457 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283356335864 : ℝ) / (2 * 0.560492364742 * 111.610931364270)) * 0.162832379411 +
        0.283356335864 ^ 2 / (2 * 0.560492364742 * 111.610931364270) := by gcongr
    _ ≤ (0.163842899802 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053064351741) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408260891)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283356335864) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12457 12457 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492364742 : ℝ) ≤ plow 12457 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.610931364270 : ℝ) ≤ √(12457 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12457 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12457 Θ 1.22 ≤ 0.011881457164 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.610931364270 := by gcongr <;> linarith
      _ ≤ (0.011881457164 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12457 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12457 12457 0.011 ≤ 0.008564457703 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12457 12457 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12457 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12457 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12457 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12457 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163842899802 + 0.011881457164 + (0.008564457703 : ℝ) *
        (1 + 2 * (0.283356335864 + 0.011881457164) / (0.560492364742 * 111.610931364270))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12457]

end BstLean.Part269.N12457

/-! The original eight local profiles supply actual 12457 moment certificates. -/
namespace BstLean.Part269.N12457
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12457 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12457 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12457 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053064351741 ∧
    0 ≤ bN 12457 BstLean.Part154.csC (groupTheta g) ∧ bN 12457 BstLean.Part154.csC (groupTheta g) ≤ 0.001408260891 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12457 12457 0.011
      (momentAllowance 12457 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12457 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12457 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12457 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12457 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12457 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230357009316 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12457 0.011
      (momentAllowance 12457 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12457 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12457
/-! The actual computed-centre upper energy formula at 12457. -/
namespace BstLean.Part269.N12457
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12457

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12457
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12457)
open BstLean.Part268 (cell12457)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086233764267
  | 2 => 0.087190996849
  | 3 => 0.088148611755
  | 4 => 0.089108533598
  | 5 => 0.090073071825
  | 6 => 0.091044975413
  | 7 => 0.092027492275
  | 8 => 0.093024433339
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12457 12457 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12457 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12457

/-! Actual upper energy certificates on all 43 source endpoints at 12457. -/
namespace BstLean.Part269.N12457
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12457)
open BstLean.Part268 (cell12457)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12457 (gMinus 12457) (1 - (cell12457 i).lower) ≤ 1 ∧
    energyUpper 12457 (gMinus 12457) (BstLean.Part211.gPlus 12457)
      (finiteEnergy 12457 12457 0.011) (1 - (cell12457 i).lower) ≤
      (cell12457 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨10,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨11,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨12,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨13,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨14,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨15,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨16,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨17,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨18,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨19,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨20,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨21,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨22,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨23,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨24,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨25,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨26,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨27,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨28,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨29,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨30,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨31,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨32,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨33,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨34,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨35,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨36,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨37,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨38,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨39,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨40,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨41,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨42,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨43,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨44,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨45,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨46,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨47,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨48,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨49,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨50,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨51,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12457) (by norm_num)
        (q := 1 - (cell12457 ⟨52,by decide⟩).lower)
        (by norm_num [cell12457]) (by norm_num [cell12457])
      exact ⟨E.1,E.2.trans (by norm_num [cell12457])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12457

/-! Source-cell containment and simple scalar guards at 12457. -/
namespace BstLean.Part269.N12457
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12457)
open BstLean.Part268 (cell12457)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12457 ⟨10,by decide⟩).lower ∧ (cell12457 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12457 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12457 ⟨11,by decide⟩).lower ∧ (cell12457 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12457 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12457 ⟨12,by decide⟩).lower ∧ (cell12457 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12457 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12457 ⟨13,by decide⟩).lower ∧ (cell12457 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12457 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12457 ⟨14,by decide⟩).lower ∧ (cell12457 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12457 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12457 ⟨15,by decide⟩).lower ∧ (cell12457 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12457 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12457 ⟨16,by decide⟩).lower ∧ (cell12457 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12457 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12457 ⟨17,by decide⟩).lower ∧ (cell12457 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12457 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12457 ⟨18,by decide⟩).lower ∧ (cell12457 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12457 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12457 ⟨19,by decide⟩).lower ∧ (cell12457 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12457 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12457 ⟨20,by decide⟩).lower ∧ (cell12457 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12457 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12457 ⟨21,by decide⟩).lower ∧ (cell12457 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12457 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12457 ⟨22,by decide⟩).lower ∧ (cell12457 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12457 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12457 ⟨23,by decide⟩).lower ∧ (cell12457 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12457 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12457 ⟨24,by decide⟩).lower ∧ (cell12457 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12457 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12457 ⟨25,by decide⟩).lower ∧ (cell12457 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12457 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12457 ⟨26,by decide⟩).lower ∧ (cell12457 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12457 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12457 ⟨27,by decide⟩).lower ∧ (cell12457 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12457 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12457 ⟨28,by decide⟩).lower ∧ (cell12457 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12457 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12457 ⟨29,by decide⟩).lower ∧ (cell12457 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12457 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12457 ⟨30,by decide⟩).lower ∧ (cell12457 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12457 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12457 ⟨31,by decide⟩).lower ∧ (cell12457 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12457 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12457 ⟨32,by decide⟩).lower ∧ (cell12457 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12457 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12457 ⟨33,by decide⟩).lower ∧ (cell12457 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12457 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12457 ⟨34,by decide⟩).lower ∧ (cell12457 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12457 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12457 ⟨35,by decide⟩).lower ∧ (cell12457 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12457 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12457 ⟨36,by decide⟩).lower ∧ (cell12457 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12457 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12457 ⟨37,by decide⟩).lower ∧ (cell12457 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12457 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12457 ⟨38,by decide⟩).lower ∧ (cell12457 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12457 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12457 ⟨39,by decide⟩).lower ∧ (cell12457 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12457 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12457 ⟨40,by decide⟩).lower ∧ (cell12457 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12457 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12457 ⟨41,by decide⟩).lower ∧ (cell12457 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12457 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12457 ⟨42,by decide⟩).lower ∧ (cell12457 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12457 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12457 ⟨43,by decide⟩).lower ∧ (cell12457 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12457 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12457 ⟨44,by decide⟩).lower ∧ (cell12457 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12457 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12457 ⟨45,by decide⟩).lower ∧ (cell12457 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12457 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12457 ⟨46,by decide⟩).lower ∧ (cell12457 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12457 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12457 ⟨47,by decide⟩).lower ∧ (cell12457 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12457 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12457 ⟨48,by decide⟩).lower ∧ (cell12457 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12457 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12457 ⟨49,by decide⟩).lower ∧ (cell12457 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12457 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12457 ⟨50,by decide⟩).lower ∧ (cell12457 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12457 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12457 ⟨51,by decide⟩).lower ∧ (cell12457 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12457 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12457 ⟨52,by decide⟩).lower ∧ (cell12457 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12457 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12457 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12457 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12457,cell12457,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12457 i).lower ∧
    (cell12457 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12457 i).upper ≤ (0.532 : ℝ) ∧
    (cell12457 i).centre ≤ (0.1 : ℝ) ∧ (cell12457 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12457 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12457 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12457

/-! The local source numeric instances at 12457 have no network premises. -/
namespace BstLean.Part269.N12457
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12457)
open BstLean.Part268 (cell12457)

noncomputable def sourceNumerics12457 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12457 (cell12457 i)
      scalarRow12457.M scalarRow12457.H scalarRow12457.xi := by
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
    energy_allowance := scalarRow12457.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12457]
    centre_nonneg := (scalarRow12457.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12457])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12457
/-! Actual 12458 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12458
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12458 ≤ (1.036158423864 : ℝ) := by
  have hr : (111.615411122299 : ℝ) ≤ √(12458 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.615411122299 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12458 12458 (11 / 1000) ≤
    (0.008564113960 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12458) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.615411122299 : ℝ) ≤ √(12458 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12458)
  have hdiv : K / √(12458 : ℝ) ≤ K / 111.615411122299 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.615411122299 ≤ (0.008564113960 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12458.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12458 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12458 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12458 := gPlus_lower 12458
end BstLean.Part269.N12458

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12458
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036158423863 : ℝ) ≤ wn 12458 := by
  have hn : √(12458 : ℝ) ≤ 111.615411122300 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12458 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.615411122300 ≤ 2 / √(12458 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256860289 : ℝ) ≤ rhoBar 12458 BstLean.Part154.csC ∧
    rhoBar 12458 BstLean.Part154.csC ≤ 0.000256860686 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036158423863 : ℝ) / (1.295212 * 12458) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036158423864 : ℝ) / (1.29521 * 12458) := by gcongr
      _ ≤ (0.000256860686 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12458 BstLean.Part154.csC) ≤ 0.001027508722 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12458 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12458 BstLean.Part154.csC) (piBar (rhoBar 12458 BstLean.Part154.csC)) ≤ 0.000196192105 ∧
    cc1 (rhoBar 12458 BstLean.Part154.csC) (piBar (rhoBar 12458 BstLean.Part154.csC)) ≤ 0.000124838302 ∧
    cc2 (rhoBar 12458 BstLean.Part154.csC) ≤ 0.000072469546 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12458 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12458 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12458 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12458 BstLean.Part154.csC * nuR (rhoBar 12458 BstLean.Part154.csC)) ≤ 0.000513737867 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256860686 : ℝ) * 0.001027508722 := by gcongr
      _ ≤ (0.000513737867 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12458 BstLean.Part154.csC) * nuR (rhoBar 12458 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001027508722 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12458 BstLean.Part154.csC) * rhoBar 12458 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256860686 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256860686 / 2 + 0.399 * 0.001027508722 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196192105 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513737867 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124838302 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256860686 / 1.414213562 := by gcongr
      _ ≤ (0.000072469546 : ℝ) := by norm_num

end BstLean.Part269.N12458

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12458
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12458 BstLean.Part154.csC) (piBar (rhoBar 12458 BstLean.Part154.csC)) ≤ 1.66226E-7 := by
  have hr0 : 0 ≤ rhoBar 12458 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12458 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12458 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12458 BstLean.Part154.csC) (piBar (rhoBar 12458 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12458 BstLean.Part154.csC) (piBar (rhoBar 12458 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12458 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196192105 : ℝ) ^ 2 + 0.000124838302 ^ 2 + 3 * 0.000072469546 ^ 2 +
        2 * 0.797885 * 0.000196192105 * 0.000124838302 + 2 * 0.000196192105 * 0.000072469546 +
        4 * 0.797885 * 0.000124838302 * 0.000072469546 := by gcongr
    _ ≤ (1.66226E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12458 BstLean.Part154.csC Θ ≤ 0.002682181366 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12458 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12458 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12458 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12458 BstLean.Part154.csC) (piBar (rhoBar 12458 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12458 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036158423864 * 1.66226E-7 / (0.000256860289 : ℝ) := by gcongr
    _ ≤ 0.002682181366 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12458 BstLean.Part154.csC Θ ≤ 0.002977020682 + 0.000677741384 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12458 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12458 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12458 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036158423864 : ℝ) * ((2 * Θ * 0.000256860686 +
        (6863 / 10000) * 0.000256860686 * 12458 * 0.001027508722) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002977020682 + 0.000677741384 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12458 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12458 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12458 0.011 Θ ∧ gammaRatio 12458 0.011 Θ ≤ 0.000088302062 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12458 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036158423864 : ℝ) * 0.525 / ((1 - 0.011) * 12458) := by gcongr
      _ ≤ (0.000088302062 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12458 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12458 0.011 Θ) :=
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
    badAllowance 12458 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12458 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12458 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12458 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12458 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12458 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12458 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12458 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12458 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12458 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12458 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036158423864 : ℝ) * 12458 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12458 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003793395428 + 0.003359922750 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12458

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12458
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12458 BstLean.Part154.csC) (piBar (rhoBar 12458 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12458 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12458 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12458 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12458 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12458 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12458 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12458 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12458 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12458 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12458 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12458 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12458 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12458 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12458 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052997176098 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12458) ≤ 0.010699576063 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12458 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036158423864)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010699576063 + 2 * 0.737676 / 12458) := by gcongr
    _ ≤ (0.052997176098 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12458 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12458

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12458
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492411743 : ℝ) ≤ plow 12458 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12458) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053063954872)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408145218) : eMP 12458 0.011 xi bn ≤ 0.001211942830 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12458 : ℝ) * (1 - 0.011))) ≤ 0.000599206304 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001408145218 / (12458 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599206304 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599206304 : ℝ) + 3.141593 * 0.053063954872 / (12458 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001211942830 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053063954872)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408145218) : PiBarMP 12458 12 0.011 xi bn ≤ 0.162825801537 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12458 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037525261066 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.999828828696 : ℝ) ≤ √((12458 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.615411122299 : ℝ) ≤ √(12458 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12458) ≤ 0.124825130533 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037525261066 + 0.053063954872 * 1.772454 / (2 * (110.999828828696 : ℝ))) * (1 + 0.001211942830) +
        8 / (12458 * 111.615411122299) + 0.124825130533 := by gcongr
    _ ≤ (0.162825801537 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053063954872)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408145218) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283353323991) :
    parallelOracle 12458 0.011 xi bn cd ≤ 0.163836248828 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12458 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12458 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492411743 : ℝ) ≤ plow 12458 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.615411122299 : ℝ) ≤ √(12458 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283353323991 : ℝ) / (2 * 0.560492411743 * 111.615411122299)) * 0.162825801537 +
        0.283353323991 ^ 2 / (2 * 0.560492411743 * 111.615411122299) := by gcongr
    _ ≤ (0.163836248828 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053063954872) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408145218)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283353323991) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12458 12458 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492411743 : ℝ) ≤ plow 12458 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.615411122299 : ℝ) ≤ √(12458 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12458 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12458 Θ 1.22 ≤ 0.011880980294 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.615411122299 := by gcongr <;> linarith
      _ ≤ (0.011880980294 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12458 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12458 12458 0.011 ≤ 0.008564113960 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12458 12458 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12458 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12458 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12458 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12458 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163836248828 + 0.011880980294 + (0.008564113960 : ℝ) *
        (1 + 2 * (0.283353323991 + 0.011880980294) / (0.560492411743 * 111.615411122299))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12458]

end BstLean.Part269.N12458

/-! The original eight local profiles supply actual 12458 moment certificates. -/
namespace BstLean.Part269.N12458
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12458 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12458 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12458 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053063954872 ∧
    0 ≤ bN 12458 BstLean.Part154.csC (groupTheta g) ∧ bN 12458 BstLean.Part154.csC (groupTheta g) ≤ 0.001408145218 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12458 12458 0.011
      (momentAllowance 12458 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12458 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12458 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12458 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12458 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12458 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230356147893 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12458 0.011
      (momentAllowance 12458 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12458 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12458
/-! The actual computed-centre upper energy formula at 12458. -/
namespace BstLean.Part269.N12458
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12458

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12458
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12458)
open BstLean.Part268 (cell12458)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086230549176
  | 2 => 0.087187715491
  | 3 => 0.088145253341
  | 4 => 0.089105084945
  | 5 => 0.090069516947
  | 6 => 0.091041295070
  | 7 => 0.092023663466
  | 8 => 0.093020428745
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12458 12458 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12458 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12458

/-! Actual upper energy certificates on all 43 source endpoints at 12458. -/
namespace BstLean.Part269.N12458
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12458)
open BstLean.Part268 (cell12458)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12458 (gMinus 12458) (1 - (cell12458 i).lower) ≤ 1 ∧
    energyUpper 12458 (gMinus 12458) (BstLean.Part211.gPlus 12458)
      (finiteEnergy 12458 12458 0.011) (1 - (cell12458 i).lower) ≤
      (cell12458 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨10,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨11,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨12,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨13,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨14,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨15,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨16,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨17,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨18,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨19,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨20,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨21,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨22,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨23,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨24,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨25,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨26,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨27,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨28,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨29,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨30,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨31,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨32,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨33,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨34,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨35,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨36,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨37,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨38,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨39,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨40,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨41,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨42,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨43,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨44,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨45,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨46,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨47,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨48,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨49,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨50,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨51,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12458) (by norm_num)
        (q := 1 - (cell12458 ⟨52,by decide⟩).lower)
        (by norm_num [cell12458]) (by norm_num [cell12458])
      exact ⟨E.1,E.2.trans (by norm_num [cell12458])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12458

/-! Source-cell containment and simple scalar guards at 12458. -/
namespace BstLean.Part269.N12458
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12458)
open BstLean.Part268 (cell12458)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12458 ⟨10,by decide⟩).lower ∧ (cell12458 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12458 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12458 ⟨11,by decide⟩).lower ∧ (cell12458 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12458 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12458 ⟨12,by decide⟩).lower ∧ (cell12458 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12458 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12458 ⟨13,by decide⟩).lower ∧ (cell12458 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12458 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12458 ⟨14,by decide⟩).lower ∧ (cell12458 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12458 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12458 ⟨15,by decide⟩).lower ∧ (cell12458 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12458 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12458 ⟨16,by decide⟩).lower ∧ (cell12458 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12458 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12458 ⟨17,by decide⟩).lower ∧ (cell12458 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12458 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12458 ⟨18,by decide⟩).lower ∧ (cell12458 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12458 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12458 ⟨19,by decide⟩).lower ∧ (cell12458 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12458 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12458 ⟨20,by decide⟩).lower ∧ (cell12458 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12458 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12458 ⟨21,by decide⟩).lower ∧ (cell12458 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12458 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12458 ⟨22,by decide⟩).lower ∧ (cell12458 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12458 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12458 ⟨23,by decide⟩).lower ∧ (cell12458 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12458 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12458 ⟨24,by decide⟩).lower ∧ (cell12458 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12458 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12458 ⟨25,by decide⟩).lower ∧ (cell12458 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12458 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12458 ⟨26,by decide⟩).lower ∧ (cell12458 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12458 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12458 ⟨27,by decide⟩).lower ∧ (cell12458 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12458 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12458 ⟨28,by decide⟩).lower ∧ (cell12458 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12458 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12458 ⟨29,by decide⟩).lower ∧ (cell12458 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12458 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12458 ⟨30,by decide⟩).lower ∧ (cell12458 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12458 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12458 ⟨31,by decide⟩).lower ∧ (cell12458 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12458 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12458 ⟨32,by decide⟩).lower ∧ (cell12458 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12458 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12458 ⟨33,by decide⟩).lower ∧ (cell12458 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12458 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12458 ⟨34,by decide⟩).lower ∧ (cell12458 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12458 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12458 ⟨35,by decide⟩).lower ∧ (cell12458 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12458 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12458 ⟨36,by decide⟩).lower ∧ (cell12458 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12458 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12458 ⟨37,by decide⟩).lower ∧ (cell12458 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12458 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12458 ⟨38,by decide⟩).lower ∧ (cell12458 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12458 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12458 ⟨39,by decide⟩).lower ∧ (cell12458 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12458 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12458 ⟨40,by decide⟩).lower ∧ (cell12458 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12458 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12458 ⟨41,by decide⟩).lower ∧ (cell12458 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12458 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12458 ⟨42,by decide⟩).lower ∧ (cell12458 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12458 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12458 ⟨43,by decide⟩).lower ∧ (cell12458 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12458 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12458 ⟨44,by decide⟩).lower ∧ (cell12458 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12458 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12458 ⟨45,by decide⟩).lower ∧ (cell12458 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12458 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12458 ⟨46,by decide⟩).lower ∧ (cell12458 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12458 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12458 ⟨47,by decide⟩).lower ∧ (cell12458 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12458 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12458 ⟨48,by decide⟩).lower ∧ (cell12458 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12458 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12458 ⟨49,by decide⟩).lower ∧ (cell12458 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12458 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12458 ⟨50,by decide⟩).lower ∧ (cell12458 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12458 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12458 ⟨51,by decide⟩).lower ∧ (cell12458 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12458 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12458 ⟨52,by decide⟩).lower ∧ (cell12458 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12458 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12458 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12458 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12458,cell12458,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12458 i).lower ∧
    (cell12458 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12458 i).upper ≤ (0.532 : ℝ) ∧
    (cell12458 i).centre ≤ (0.1 : ℝ) ∧ (cell12458 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12458 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12458 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12458

/-! The local source numeric instances at 12458 have no network premises. -/
namespace BstLean.Part269.N12458
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12458)
open BstLean.Part268 (cell12458)

noncomputable def sourceNumerics12458 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12458 (cell12458 i)
      scalarRow12458.M scalarRow12458.H scalarRow12458.xi := by
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
    energy_allowance := scalarRow12458.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12458]
    centre_nonneg := (scalarRow12458.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12458])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12458
/-! Actual 12459 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12459
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12459 ≤ (1.036156959853 : ℝ) := by
  have hr : (111.619890700537 : ℝ) ≤ √(12459 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.619890700537 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12459 12459 (11 / 1000) ≤
    (0.008563770258 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12459) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.619890700537 : ℝ) ≤ √(12459 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12459)
  have hdiv : K / √(12459 : ℝ) ≤ K / 111.619890700537 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.619890700537 ≤ (0.008563770258 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12459.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12459 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12459 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12459 := gPlus_lower 12459
end BstLean.Part269.N12459

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12459
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036156959852 : ℝ) ≤ wn 12459 := by
  have hn : √(12459 : ℝ) ≤ 111.619890700538 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12459 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.619890700538 ≤ 2 / √(12459 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256839310 : ℝ) ≤ rhoBar 12459 BstLean.Part154.csC ∧
    rhoBar 12459 BstLean.Part154.csC ≤ 0.000256839707 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036156959852 : ℝ) / (1.295212 * 12459) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036156959853 : ℝ) / (1.29521 * 12459) := by gcongr
      _ ≤ (0.000256839707 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12459 BstLean.Part154.csC) ≤ 0.001027424795 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12459 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12459 BstLean.Part154.csC) (piBar (rhoBar 12459 BstLean.Part154.csC)) ≤ 0.000196176081 ∧
    cc1 (rhoBar 12459 BstLean.Part154.csC) (piBar (rhoBar 12459 BstLean.Part154.csC)) ≤ 0.000124828106 ∧
    cc2 (rhoBar 12459 BstLean.Part154.csC) ≤ 0.000072463627 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12459 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12459 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12459 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12459 BstLean.Part154.csC * nuR (rhoBar 12459 BstLean.Part154.csC)) ≤ 0.000513695906 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256839707 : ℝ) * 0.001027424795 := by gcongr
      _ ≤ (0.000513695906 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12459 BstLean.Part154.csC) * nuR (rhoBar 12459 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001027424795 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12459 BstLean.Part154.csC) * rhoBar 12459 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256839707 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256839707 / 2 + 0.399 * 0.001027424795 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196176081 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513695906 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124828106 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256839707 / 1.414213562 := by gcongr
      _ ≤ (0.000072463627 : ℝ) := by norm_num

end BstLean.Part269.N12459

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12459
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12459 BstLean.Part154.csC) (piBar (rhoBar 12459 BstLean.Part154.csC)) ≤ 1.66199E-7 := by
  have hr0 : 0 ≤ rhoBar 12459 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12459 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12459 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12459 BstLean.Part154.csC) (piBar (rhoBar 12459 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12459 BstLean.Part154.csC) (piBar (rhoBar 12459 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12459 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196176081 : ℝ) ^ 2 + 0.000124828106 ^ 2 + 3 * 0.000072463627 ^ 2 +
        2 * 0.797885 * 0.000196176081 * 0.000124828106 + 2 * 0.000196176081 * 0.000072463627 +
        4 * 0.797885 * 0.000124828106 * 0.000072463627 := by gcongr
    _ ≤ (1.66199E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12459 BstLean.Part154.csC Θ ≤ 0.002681960960 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12459 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12459 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12459 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12459 BstLean.Part154.csC) (piBar (rhoBar 12459 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12459 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036156959853 * 1.66199E-7 / (0.000256839310 : ℝ) := by gcongr
    _ ≤ 0.002681960960 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12459 BstLean.Part154.csC Θ ≤ 0.002976769111 + 0.000677685072 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12459 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12459 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12459 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036156959853 : ℝ) * ((2 * Θ * 0.000256839707 +
        (6863 / 10000) * 0.000256839707 * 12459 * 0.001027424795) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002976769111 + 0.000677685072 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12459 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12459 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12459 0.011 Θ ∧ gammaRatio 12459 0.011 Θ ≤ 0.000088294850 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12459 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036156959853 : ℝ) * 0.525 / ((1 - 0.011) * 12459) := by gcongr
      _ ≤ (0.000088294850 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12459 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12459 0.011 Θ) :=
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
    badAllowance 12459 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12459 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12459 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12459 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12459 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12459 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12459 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12459 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12459 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12459 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12459 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036156959853 : ℝ) * 12459 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12459 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003793143857 + 0.003359646032 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12459

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12459
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12459 BstLean.Part154.csC) (piBar (rhoBar 12459 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12459 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12459 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12459 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12459 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12459 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12459 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12459 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12459 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12459 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12459 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12459 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12459 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12459 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12459 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052995025910 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12459) ≤ 0.010699146663 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12459 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036156959853)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010699146663 + 2 * 0.737676 / 12459) := by gcongr
    _ ≤ (0.052995025910 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12459 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12459

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12459
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492458736 : ℝ) ≤ plow 12459 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12459) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053063558024)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408029504) : eMP 12459 0.011 xi bn ≤ 0.001211844309 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12459 : ℝ) * (1 - 0.011))) ≤ 0.000599157637 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001408029504 / (12459 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599157637 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599157637 : ℝ) + 3.141593 * 0.053063558024 / (12459 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001211844309 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053063558024)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408029504) : PiBarMP 12459 12 0.011 xi bn ≤ 0.162819223658 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12459 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037523719219 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.004283701125 : ℝ) ≤ √((12459 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.619890700537 : ℝ) ≤ √(12459 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12459) ≤ 0.124820120996 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037523719219 + 0.053063558024 * 1.772454 / (2 * (111.004283701125 : ℝ))) * (1 + 0.001211844309) +
        8 / (12459 * 111.619890700537) + 0.124820120996 := by gcongr
    _ ≤ (0.162819223658 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053063558024)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408029504) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283350312422) :
    parallelOracle 12459 0.011 xi bn cd ≤ 0.163829597857 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12459 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12459 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492458736 : ℝ) ≤ plow 12459 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.619890700537 : ℝ) ≤ √(12459 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283350312422 : ℝ) / (2 * 0.560492458736 * 111.619890700537)) * 0.162819223658 +
        0.283350312422 ^ 2 / (2 * 0.560492458736 * 111.619890700537) := by gcongr
    _ ≤ (0.163829597857 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053063558024) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001408029504)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283350312422) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12459 12459 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492458736 : ℝ) ≤ plow 12459 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.619890700537 : ℝ) ≤ √(12459 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12459 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12459 Θ 1.22 ≤ 0.011880503481 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.619890700537 := by gcongr <;> linarith
      _ ≤ (0.011880503481 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12459 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12459 12459 0.011 ≤ 0.008563770258 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12459 12459 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12459 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12459 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12459 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12459 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163829597857 + 0.011880503481 + (0.008563770258 : ℝ) *
        (1 + 2 * (0.283350312422 + 0.011880503481) / (0.560492458736 * 111.619890700537))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12459]

end BstLean.Part269.N12459

/-! The original eight local profiles supply actual 12459 moment certificates. -/
namespace BstLean.Part269.N12459
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12459 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12459 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12459 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053063558024 ∧
    0 ≤ bN 12459 BstLean.Part154.csC (groupTheta g) ∧ bN 12459 BstLean.Part154.csC (groupTheta g) ≤ 0.001408029504 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12459 12459 0.011
      (momentAllowance 12459 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12459 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12459 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12459 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12459 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12459 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230355286512 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12459 0.011
      (momentAllowance 12459 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12459 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12459
/-! The actual computed-centre upper energy formula at 12459. -/
namespace BstLean.Part269.N12459
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12459

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12459
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12459)
open BstLean.Part268 (cell12459)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086227335480
  | 2 => 0.087184435590
  | 3 => 0.088141896459
  | 4 => 0.089101637916
  | 5 => 0.090065963807
  | 6 => 0.091037616601
  | 7 => 0.092019836695
  | 8 => 0.093016426387
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12459 12459 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12459 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12459

/-! Actual upper energy certificates on all 43 source endpoints at 12459. -/
namespace BstLean.Part269.N12459
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12459)
open BstLean.Part268 (cell12459)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12459 (gMinus 12459) (1 - (cell12459 i).lower) ≤ 1 ∧
    energyUpper 12459 (gMinus 12459) (BstLean.Part211.gPlus 12459)
      (finiteEnergy 12459 12459 0.011) (1 - (cell12459 i).lower) ≤
      (cell12459 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨10,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨11,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨12,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨13,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨14,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨15,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨16,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨17,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨18,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨19,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨20,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨21,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨22,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨23,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨24,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨25,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨26,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨27,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨28,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨29,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨30,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨31,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨32,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨33,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨34,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨35,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨36,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨37,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨38,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨39,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨40,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨41,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨42,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨43,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨44,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨45,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨46,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨47,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨48,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨49,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨50,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨51,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12459) (by norm_num)
        (q := 1 - (cell12459 ⟨52,by decide⟩).lower)
        (by norm_num [cell12459]) (by norm_num [cell12459])
      exact ⟨E.1,E.2.trans (by norm_num [cell12459])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12459

/-! Source-cell containment and simple scalar guards at 12459. -/
namespace BstLean.Part269.N12459
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12459)
open BstLean.Part268 (cell12459)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12459 ⟨10,by decide⟩).lower ∧ (cell12459 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12459 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12459 ⟨11,by decide⟩).lower ∧ (cell12459 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12459 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12459 ⟨12,by decide⟩).lower ∧ (cell12459 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12459 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12459 ⟨13,by decide⟩).lower ∧ (cell12459 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12459 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12459 ⟨14,by decide⟩).lower ∧ (cell12459 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12459 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12459 ⟨15,by decide⟩).lower ∧ (cell12459 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12459 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12459 ⟨16,by decide⟩).lower ∧ (cell12459 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12459 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12459 ⟨17,by decide⟩).lower ∧ (cell12459 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12459 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12459 ⟨18,by decide⟩).lower ∧ (cell12459 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12459 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12459 ⟨19,by decide⟩).lower ∧ (cell12459 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12459 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12459 ⟨20,by decide⟩).lower ∧ (cell12459 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12459 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12459 ⟨21,by decide⟩).lower ∧ (cell12459 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12459 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12459 ⟨22,by decide⟩).lower ∧ (cell12459 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12459 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12459 ⟨23,by decide⟩).lower ∧ (cell12459 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12459 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12459 ⟨24,by decide⟩).lower ∧ (cell12459 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12459 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12459 ⟨25,by decide⟩).lower ∧ (cell12459 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12459 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12459 ⟨26,by decide⟩).lower ∧ (cell12459 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12459 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12459 ⟨27,by decide⟩).lower ∧ (cell12459 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12459 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12459 ⟨28,by decide⟩).lower ∧ (cell12459 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12459 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12459 ⟨29,by decide⟩).lower ∧ (cell12459 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12459 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12459 ⟨30,by decide⟩).lower ∧ (cell12459 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12459 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12459 ⟨31,by decide⟩).lower ∧ (cell12459 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12459 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12459 ⟨32,by decide⟩).lower ∧ (cell12459 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12459 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12459 ⟨33,by decide⟩).lower ∧ (cell12459 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12459 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12459 ⟨34,by decide⟩).lower ∧ (cell12459 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12459 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12459 ⟨35,by decide⟩).lower ∧ (cell12459 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12459 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12459 ⟨36,by decide⟩).lower ∧ (cell12459 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12459 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12459 ⟨37,by decide⟩).lower ∧ (cell12459 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12459 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12459 ⟨38,by decide⟩).lower ∧ (cell12459 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12459 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12459 ⟨39,by decide⟩).lower ∧ (cell12459 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12459 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12459 ⟨40,by decide⟩).lower ∧ (cell12459 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12459 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12459 ⟨41,by decide⟩).lower ∧ (cell12459 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12459 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12459 ⟨42,by decide⟩).lower ∧ (cell12459 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12459 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12459 ⟨43,by decide⟩).lower ∧ (cell12459 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12459 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12459 ⟨44,by decide⟩).lower ∧ (cell12459 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12459 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12459 ⟨45,by decide⟩).lower ∧ (cell12459 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12459 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12459 ⟨46,by decide⟩).lower ∧ (cell12459 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12459 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12459 ⟨47,by decide⟩).lower ∧ (cell12459 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12459 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12459 ⟨48,by decide⟩).lower ∧ (cell12459 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12459 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12459 ⟨49,by decide⟩).lower ∧ (cell12459 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12459 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12459 ⟨50,by decide⟩).lower ∧ (cell12459 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12459 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12459 ⟨51,by decide⟩).lower ∧ (cell12459 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12459 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12459 ⟨52,by decide⟩).lower ∧ (cell12459 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12459 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12459 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12459 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12459,cell12459,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12459 i).lower ∧
    (cell12459 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12459 i).upper ≤ (0.532 : ℝ) ∧
    (cell12459 i).centre ≤ (0.1 : ℝ) ∧ (cell12459 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12459 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12459 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12459

/-! The local source numeric instances at 12459 have no network premises. -/
namespace BstLean.Part269.N12459
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12459)
open BstLean.Part268 (cell12459)

noncomputable def sourceNumerics12459 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12459 (cell12459 i)
      scalarRow12459.M scalarRow12459.H scalarRow12459.xi := by
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
    energy_allowance := scalarRow12459.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12459]
    centre_nonneg := (scalarRow12459.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12459])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12459
/-! Actual 12460 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12460
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12460 ≤ (1.036155496019 : ℝ) := by
  have hr : (111.624370099006 : ℝ) ≤ √(12460 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.624370099006 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12460 12460 (11 / 1000) ≤
    (0.008563426598 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12460) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.624370099006 : ℝ) ≤ √(12460 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12460)
  have hdiv : K / √(12460 : ℝ) ≤ K / 111.624370099006 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.624370099006 ≤ (0.008563426598 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12460.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12460 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12460 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12460 := gPlus_lower 12460
end BstLean.Part269.N12460

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12460
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036155496018 : ℝ) ≤ wn 12460 := by
  have hn : √(12460 : ℝ) ≤ 111.624370099007 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12460 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.624370099007 ≤ 2 / √(12460 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256818334 : ℝ) ≤ rhoBar 12460 BstLean.Part154.csC ∧
    rhoBar 12460 BstLean.Part154.csC ≤ 0.000256818731 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036155496018 : ℝ) / (1.295212 * 12460) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036155496019 : ℝ) / (1.29521 * 12460) := by gcongr
      _ ≤ (0.000256818731 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12460 BstLean.Part154.csC) ≤ 0.001027340880 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12460 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12460 BstLean.Part154.csC) (piBar (rhoBar 12460 BstLean.Part154.csC)) ≤ 0.000196160058 ∧
    cc1 (rhoBar 12460 BstLean.Part154.csC) (piBar (rhoBar 12460 BstLean.Part154.csC)) ≤ 0.000124817911 ∧
    cc2 (rhoBar 12460 BstLean.Part154.csC) ≤ 0.000072457709 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12460 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12460 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12460 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12460 BstLean.Part154.csC * nuR (rhoBar 12460 BstLean.Part154.csC)) ≤ 0.000513653951 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256818731 : ℝ) * 0.001027340880 := by gcongr
      _ ≤ (0.000513653951 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12460 BstLean.Part154.csC) * nuR (rhoBar 12460 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001027340880 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12460 BstLean.Part154.csC) * rhoBar 12460 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256818731 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256818731 / 2 + 0.399 * 0.001027340880 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196160058 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513653951 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124817911 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256818731 / 1.414213562 := by gcongr
      _ ≤ (0.000072457709 : ℝ) := by norm_num

end BstLean.Part269.N12460

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12460
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12460 BstLean.Part154.csC) (piBar (rhoBar 12460 BstLean.Part154.csC)) ≤ 1.66171E-7 := by
  have hr0 : 0 ≤ rhoBar 12460 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12460 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12460 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12460 BstLean.Part154.csC) (piBar (rhoBar 12460 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12460 BstLean.Part154.csC) (piBar (rhoBar 12460 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12460 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196160058 : ℝ) ^ 2 + 0.000124817911 ^ 2 + 3 * 0.000072457709 ^ 2 +
        2 * 0.797885 * 0.000196160058 * 0.000124817911 + 2 * 0.000196160058 * 0.000072457709 +
        4 * 0.797885 * 0.000124817911 * 0.000072457709 := by gcongr
    _ ≤ (1.66171E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12460 BstLean.Part154.csC Θ ≤ 0.002681724350 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12460 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12460 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12460 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12460 BstLean.Part154.csC) (piBar (rhoBar 12460 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12460 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036155496019 * 1.66171E-7 / (0.000256818334 : ℝ) := by gcongr
    _ ≤ 0.002681724350 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12460 BstLean.Part154.csC Θ ≤ 0.002976517572 + 0.000677628769 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12460 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12460 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12460 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036155496019 : ℝ) * ((2 * Θ * 0.000256818731 +
        (6863 / 10000) * 0.000256818731 * 12460 * 0.001027340880) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002976517572 + 0.000677628769 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12460 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12460 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12460 0.011 Θ ∧ gammaRatio 12460 0.011 Θ ≤ 0.000088287639 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12460 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036155496019 : ℝ) * 0.525 / ((1 - 0.011) * 12460) := by gcongr
      _ ≤ (0.000088287639 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12460 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12460 0.011 Θ) :=
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
    badAllowance 12460 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12460 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12460 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12460 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12460 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12460 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12460 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12460 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12460 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12460 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12460 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036155496019 : ℝ) * 12460 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12460 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003792892318 + 0.003359353119 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12460

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12460
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12460 BstLean.Part154.csC) (piBar (rhoBar 12460 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12460 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12460 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12460 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12460 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12460 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12460 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12460 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12460 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12460 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12460 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12460 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12460 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12460 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12460 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052992875984 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12460) ≤ 0.010698717315 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12460 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036155496019)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010698717315 + 2 * 0.737676 / 12460) := by gcongr
    _ ≤ (0.052992875984 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12460 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12460

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12460
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492505722 : ℝ) ≤ plow 12460 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12460) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053063152706)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407905284) : eMP 12460 0.011 xi bn ≤ 0.001211742174 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12460 : ℝ) * (1 - 0.011))) ≤ 0.000599107164 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001407905284 / (12460 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599107164 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599107164 : ℝ) + 3.141593 * 0.053063152706 / (12460 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001211742174 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053063152706)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407905284) : PiBarMP 12460 12 0.011 xi bn ≤ 0.162812532633 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12460 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037522063963 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.008738394776 : ℝ) ≤ √((12460 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.624370099006 : ℝ) ≤ √(12460 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12460) ≤ 0.124815112062 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037522063963 + 0.053063152706 * 1.772454 / (2 * (111.008738394776 : ℝ))) * (1 + 0.001211742174) +
        8 / (12460 * 111.624370099006) + 0.124815112062 := by gcongr
    _ ≤ (0.162812532633 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053063152706)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407905284) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283347282728) :
    parallelOracle 12460 0.011 xi bn cd ≤ 0.163822833387 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12460 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12460 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492505722 : ℝ) ≤ plow 12460 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.624370099006 : ℝ) ≤ √(12460 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283347282728 : ℝ) / (2 * 0.560492505722 * 111.624370099006)) * 0.162812532633 +
        0.283347282728 ^ 2 / (2 * 0.560492505722 * 111.624370099006) := by gcongr
    _ ≤ (0.163822833387 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053063152706) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407905284)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283347282728) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12460 12460 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492505722 : ℝ) ≤ plow 12460 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.624370099006 : ℝ) ≤ √(12460 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12460 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12460 Θ 1.22 ≤ 0.011880026726 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.624370099006 := by gcongr <;> linarith
      _ ≤ (0.011880026726 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12460 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12460 12460 0.011 ≤ 0.008563426598 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12460 12460 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12460 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12460 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12460 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12460 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163822833387 + 0.011880026726 + (0.008563426598 : ℝ) *
        (1 + 2 * (0.283347282728 + 0.011880026726) / (0.560492505722 * 111.624370099006))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12460]

end BstLean.Part269.N12460

/-! The original eight local profiles supply actual 12460 moment certificates. -/
namespace BstLean.Part269.N12460
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12460 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12460 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12460 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053063152706 ∧
    0 ≤ bN 12460 BstLean.Part154.csC (groupTheta g) ∧ bN 12460 BstLean.Part154.csC (groupTheta g) ≤ 0.001407905284 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12460 12460 0.011
      (momentAllowance 12460 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12460 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12460 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12460 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12460 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12460 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230354406744 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12460 0.011
      (momentAllowance 12460 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12460 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12460
/-! The actual computed-centre upper energy formula at 12460. -/
namespace BstLean.Part269.N12460
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12460

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12460
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12460)
open BstLean.Part268 (cell12460)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086224123179
  | 2 => 0.087181157144
  | 3 => 0.088138541108
  | 4 => 0.089098192510
  | 5 => 0.090062412402
  | 6 => 0.091033940003
  | 7 => 0.092016011959
  | 8 => 0.093012426261
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12460 12460 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12460 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12460

/-! Actual upper energy certificates on all 43 source endpoints at 12460. -/
namespace BstLean.Part269.N12460
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12460)
open BstLean.Part268 (cell12460)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12460 (gMinus 12460) (1 - (cell12460 i).lower) ≤ 1 ∧
    energyUpper 12460 (gMinus 12460) (BstLean.Part211.gPlus 12460)
      (finiteEnergy 12460 12460 0.011) (1 - (cell12460 i).lower) ≤
      (cell12460 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨10,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨11,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨12,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨13,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨14,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨15,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨16,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨17,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨18,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨19,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨20,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨21,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨22,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨23,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨24,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨25,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨26,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨27,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨28,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨29,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨30,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨31,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨32,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨33,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨34,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨35,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨36,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨37,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨38,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨39,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨40,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨41,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨42,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨43,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨44,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨45,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨46,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨47,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨48,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨49,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨50,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨51,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12460) (by norm_num)
        (q := 1 - (cell12460 ⟨52,by decide⟩).lower)
        (by norm_num [cell12460]) (by norm_num [cell12460])
      exact ⟨E.1,E.2.trans (by norm_num [cell12460])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12460

/-! Source-cell containment and simple scalar guards at 12460. -/
namespace BstLean.Part269.N12460
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12460)
open BstLean.Part268 (cell12460)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12460 ⟨10,by decide⟩).lower ∧ (cell12460 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12460 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12460 ⟨11,by decide⟩).lower ∧ (cell12460 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12460 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12460 ⟨12,by decide⟩).lower ∧ (cell12460 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12460 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12460 ⟨13,by decide⟩).lower ∧ (cell12460 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12460 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12460 ⟨14,by decide⟩).lower ∧ (cell12460 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12460 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12460 ⟨15,by decide⟩).lower ∧ (cell12460 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12460 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12460 ⟨16,by decide⟩).lower ∧ (cell12460 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12460 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12460 ⟨17,by decide⟩).lower ∧ (cell12460 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12460 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12460 ⟨18,by decide⟩).lower ∧ (cell12460 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12460 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12460 ⟨19,by decide⟩).lower ∧ (cell12460 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12460 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12460 ⟨20,by decide⟩).lower ∧ (cell12460 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12460 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12460 ⟨21,by decide⟩).lower ∧ (cell12460 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12460 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12460 ⟨22,by decide⟩).lower ∧ (cell12460 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12460 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12460 ⟨23,by decide⟩).lower ∧ (cell12460 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12460 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12460 ⟨24,by decide⟩).lower ∧ (cell12460 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12460 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12460 ⟨25,by decide⟩).lower ∧ (cell12460 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12460 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12460 ⟨26,by decide⟩).lower ∧ (cell12460 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12460 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12460 ⟨27,by decide⟩).lower ∧ (cell12460 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12460 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12460 ⟨28,by decide⟩).lower ∧ (cell12460 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12460 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12460 ⟨29,by decide⟩).lower ∧ (cell12460 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12460 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12460 ⟨30,by decide⟩).lower ∧ (cell12460 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12460 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12460 ⟨31,by decide⟩).lower ∧ (cell12460 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12460 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12460 ⟨32,by decide⟩).lower ∧ (cell12460 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12460 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12460 ⟨33,by decide⟩).lower ∧ (cell12460 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12460 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12460 ⟨34,by decide⟩).lower ∧ (cell12460 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12460 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12460 ⟨35,by decide⟩).lower ∧ (cell12460 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12460 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12460 ⟨36,by decide⟩).lower ∧ (cell12460 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12460 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12460 ⟨37,by decide⟩).lower ∧ (cell12460 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12460 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12460 ⟨38,by decide⟩).lower ∧ (cell12460 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12460 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12460 ⟨39,by decide⟩).lower ∧ (cell12460 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12460 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12460 ⟨40,by decide⟩).lower ∧ (cell12460 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12460 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12460 ⟨41,by decide⟩).lower ∧ (cell12460 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12460 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12460 ⟨42,by decide⟩).lower ∧ (cell12460 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12460 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12460 ⟨43,by decide⟩).lower ∧ (cell12460 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12460 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12460 ⟨44,by decide⟩).lower ∧ (cell12460 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12460 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12460 ⟨45,by decide⟩).lower ∧ (cell12460 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12460 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12460 ⟨46,by decide⟩).lower ∧ (cell12460 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12460 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12460 ⟨47,by decide⟩).lower ∧ (cell12460 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12460 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12460 ⟨48,by decide⟩).lower ∧ (cell12460 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12460 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12460 ⟨49,by decide⟩).lower ∧ (cell12460 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12460 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12460 ⟨50,by decide⟩).lower ∧ (cell12460 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12460 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12460 ⟨51,by decide⟩).lower ∧ (cell12460 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12460 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12460 ⟨52,by decide⟩).lower ∧ (cell12460 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12460 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12460 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12460 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12460,cell12460,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12460 i).lower ∧
    (cell12460 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12460 i).upper ≤ (0.532 : ℝ) ∧
    (cell12460 i).centre ≤ (0.1 : ℝ) ∧ (cell12460 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12460 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12460 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12460

/-! The local source numeric instances at 12460 have no network premises. -/
namespace BstLean.Part269.N12460
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12460)
open BstLean.Part268 (cell12460)

noncomputable def sourceNumerics12460 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12460 (cell12460 i)
      scalarRow12460.M scalarRow12460.H scalarRow12460.xi := by
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
    energy_allowance := scalarRow12460.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12460]
    centre_nonneg := (scalarRow12460.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12460])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12460
/-! Actual 12461 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12461
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12461 ≤ (1.036154032363 : ℝ) := by
  have hr : (111.628849317727 : ℝ) ≤ √(12461 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.628849317727 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12461 12461 (11 / 1000) ≤
    (0.008563082979 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12461) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.628849317727 : ℝ) ≤ √(12461 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12461)
  have hdiv : K / √(12461 : ℝ) ≤ K / 111.628849317727 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.628849317727 ≤ (0.008563082979 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12461.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12461 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12461 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12461 := gPlus_lower 12461
end BstLean.Part269.N12461

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12461
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036154032362 : ℝ) ≤ wn 12461 := by
  have hn : √(12461 : ℝ) ≤ 111.628849317728 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12461 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.628849317728 ≤ 2 / √(12461 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256797361 : ℝ) ≤ rhoBar 12461 BstLean.Part154.csC ∧
    rhoBar 12461 BstLean.Part154.csC ≤ 0.000256797759 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036154032362 : ℝ) / (1.295212 * 12461) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036154032363 : ℝ) / (1.29521 * 12461) := by gcongr
      _ ≤ (0.000256797759 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12461 BstLean.Part154.csC) ≤ 0.001027256982 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12461 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12461 BstLean.Part154.csC) (piBar (rhoBar 12461 BstLean.Part154.csC)) ≤ 0.000196144039 ∧
    cc1 (rhoBar 12461 BstLean.Part154.csC) (piBar (rhoBar 12461 BstLean.Part154.csC)) ≤ 0.000124807718 ∧
    cc2 (rhoBar 12461 BstLean.Part154.csC) ≤ 0.000072451792 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12461 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12461 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12461 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12461 BstLean.Part154.csC * nuR (rhoBar 12461 BstLean.Part154.csC)) ≤ 0.000513612005 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256797759 : ℝ) * 0.001027256982 := by gcongr
      _ ≤ (0.000513612005 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12461 BstLean.Part154.csC) * nuR (rhoBar 12461 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001027256982 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12461 BstLean.Part154.csC) * rhoBar 12461 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256797759 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256797759 / 2 + 0.399 * 0.001027256982 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196144039 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513612005 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124807718 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256797759 / 1.414213562 := by gcongr
      _ ≤ (0.000072451792 : ℝ) := by norm_num

end BstLean.Part269.N12461

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12461
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12461 BstLean.Part154.csC) (piBar (rhoBar 12461 BstLean.Part154.csC)) ≤ 1.66144E-7 := by
  have hr0 : 0 ≤ rhoBar 12461 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12461 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12461 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12461 BstLean.Part154.csC) (piBar (rhoBar 12461 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12461 BstLean.Part154.csC) (piBar (rhoBar 12461 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12461 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196144039 : ℝ) ^ 2 + 0.000124807718 ^ 2 + 3 * 0.000072451792 ^ 2 +
        2 * 0.797885 * 0.000196144039 * 0.000124807718 + 2 * 0.000196144039 * 0.000072451792 +
        4 * 0.797885 * 0.000124807718 * 0.000072451792 := by gcongr
    _ ≤ (1.66144E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12461 BstLean.Part154.csC Θ ≤ 0.002681503812 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12461 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12461 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12461 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12461 BstLean.Part154.csC) (piBar (rhoBar 12461 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12461 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036154032363 * 1.66144E-7 / (0.000256797361 : ℝ) := by gcongr
    _ ≤ 0.002681503812 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12461 BstLean.Part154.csC Θ ≤ 0.002976266092 + 0.000677572476 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12461 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12461 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12461 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036154032363 : ℝ) * ((2 * Θ * 0.000256797759 +
        (6863 / 10000) * 0.000256797759 * 12461 * 0.001027256982) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002976266092 + 0.000677572476 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12461 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12461 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12461 0.011 Θ ∧ gammaRatio 12461 0.011 Θ ≤ 0.000088280429 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12461 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036154032363 : ℝ) * 0.525 / ((1 - 0.011) * 12461) := by gcongr
      _ ≤ (0.000088280429 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12461 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12461 0.011 Θ) :=
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
    badAllowance 12461 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12461 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12461 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12461 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12461 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12461 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12461 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12461 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12461 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12461 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12461 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036154032363 : ℝ) * 12461 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12461 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003792640838 + 0.003359076288 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12461

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12461
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12461 BstLean.Part154.csC) (piBar (rhoBar 12461 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12461 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12461 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12461 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12461 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12461 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12461 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12461 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12461 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12461 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12461 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12461 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12461 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12461 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12461 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052990726315 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12461) ≤ 0.010698288018 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12461 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036154032363)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010698288018 + 2 * 0.737676 / 12461) := by gcongr
    _ ≤ (0.052990726315 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12461 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12461

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12461
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492552700 : ℝ) ≤ plow 12461 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12461) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053062755890)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407789502) : eMP 12461 0.011 xi bn ≤ 0.001211643641 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12461 : ℝ) * (1 - 0.011))) ≤ 0.000599058491 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001407789502 / (12461 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599058491 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599058491 : ℝ) + 3.141593 * 0.053062755890 / (12461 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001211643641 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053062755890)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407789502) : PiBarMP 12461 12 0.011 xi bn ≤ 0.162805954928 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12461 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037520521079 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.013192909671 : ℝ) ≤ √((12461 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.628849317727 : ℝ) ≤ √(12461 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12461) ≤ 0.124810103732 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037520521079 + 0.053062755890 * 1.772454 / (2 * (111.013192909671 : ℝ))) * (1 + 0.001211643641) +
        8 / (12461 * 111.628849317727) + 0.124810103732 := by gcongr
    _ ≤ (0.162805954928 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053062755890)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407789502) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283344271741) :
    parallelOracle 12461 0.011 xi bn cd ≤ 0.163816182611 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12461 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12461 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492552700 : ℝ) ≤ plow 12461 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.628849317727 : ℝ) ≤ √(12461 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283344271741 : ℝ) / (2 * 0.560492552700 * 111.628849317727)) * 0.162805954928 +
        0.283344271741 ^ 2 / (2 * 0.560492552700 * 111.628849317727) := by gcongr
    _ ≤ (0.163816182611 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053062755890) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407789502)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283344271741) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12461 12461 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492552700 : ℝ) ≤ plow 12461 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.628849317727 : ℝ) ≤ √(12461 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12461 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12461 Θ 1.22 ≤ 0.011879550028 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.628849317727 := by gcongr <;> linarith
      _ ≤ (0.011879550028 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12461 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12461 12461 0.011 ≤ 0.008563082979 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12461 12461 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12461 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12461 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12461 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12461 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163816182611 + 0.011879550028 + (0.008563082979 : ℝ) *
        (1 + 2 * (0.283344271741 + 0.011879550028) / (0.560492552700 * 111.628849317727))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12461]

end BstLean.Part269.N12461

/-! The original eight local profiles supply actual 12461 moment certificates. -/
namespace BstLean.Part269.N12461
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12461 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12461 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12461 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053062755890 ∧
    0 ≤ bN 12461 BstLean.Part154.csC (groupTheta g) ∧ bN 12461 BstLean.Part154.csC (groupTheta g) ≤ 0.001407789502 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12461 12461 0.011
      (momentAllowance 12461 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12461 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12461 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12461 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12461 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12461 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230353545426 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12461 0.011
      (momentAllowance 12461 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12461 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12461
/-! The actual computed-centre upper energy formula at 12461. -/
namespace BstLean.Part269.N12461
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12461

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12461
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12461)
open BstLean.Part268 (cell12461)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086220912271
  | 2 => 0.087177880152
  | 3 => 0.088135187285
  | 4 => 0.089094748725
  | 5 => 0.090058862730
  | 6 => 0.091030265274
  | 7 => 0.092012189257
  | 8 => 0.093008428366
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12461 12461 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12461 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12461

/-! Actual upper energy certificates on all 43 source endpoints at 12461. -/
namespace BstLean.Part269.N12461
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12461)
open BstLean.Part268 (cell12461)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12461 (gMinus 12461) (1 - (cell12461 i).lower) ≤ 1 ∧
    energyUpper 12461 (gMinus 12461) (BstLean.Part211.gPlus 12461)
      (finiteEnergy 12461 12461 0.011) (1 - (cell12461 i).lower) ≤
      (cell12461 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨10,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨11,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨12,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨13,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨14,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨15,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨16,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨17,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨18,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨19,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨20,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨21,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨22,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨23,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨24,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨25,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨26,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨27,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨28,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨29,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨30,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨31,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨32,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨33,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨34,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨35,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨36,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨37,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨38,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨39,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨40,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨41,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨42,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨43,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨44,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨45,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨46,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨47,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨48,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨49,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨50,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨51,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12461) (by norm_num)
        (q := 1 - (cell12461 ⟨52,by decide⟩).lower)
        (by norm_num [cell12461]) (by norm_num [cell12461])
      exact ⟨E.1,E.2.trans (by norm_num [cell12461])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12461

/-! Source-cell containment and simple scalar guards at 12461. -/
namespace BstLean.Part269.N12461
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12461)
open BstLean.Part268 (cell12461)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12461 ⟨10,by decide⟩).lower ∧ (cell12461 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12461 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12461 ⟨11,by decide⟩).lower ∧ (cell12461 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12461 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12461 ⟨12,by decide⟩).lower ∧ (cell12461 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12461 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12461 ⟨13,by decide⟩).lower ∧ (cell12461 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12461 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12461 ⟨14,by decide⟩).lower ∧ (cell12461 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12461 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12461 ⟨15,by decide⟩).lower ∧ (cell12461 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12461 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12461 ⟨16,by decide⟩).lower ∧ (cell12461 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12461 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12461 ⟨17,by decide⟩).lower ∧ (cell12461 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12461 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12461 ⟨18,by decide⟩).lower ∧ (cell12461 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12461 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12461 ⟨19,by decide⟩).lower ∧ (cell12461 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12461 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12461 ⟨20,by decide⟩).lower ∧ (cell12461 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12461 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12461 ⟨21,by decide⟩).lower ∧ (cell12461 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12461 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12461 ⟨22,by decide⟩).lower ∧ (cell12461 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12461 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12461 ⟨23,by decide⟩).lower ∧ (cell12461 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12461 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12461 ⟨24,by decide⟩).lower ∧ (cell12461 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12461 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12461 ⟨25,by decide⟩).lower ∧ (cell12461 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12461 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12461 ⟨26,by decide⟩).lower ∧ (cell12461 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12461 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12461 ⟨27,by decide⟩).lower ∧ (cell12461 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12461 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12461 ⟨28,by decide⟩).lower ∧ (cell12461 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12461 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12461 ⟨29,by decide⟩).lower ∧ (cell12461 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12461 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12461 ⟨30,by decide⟩).lower ∧ (cell12461 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12461 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12461 ⟨31,by decide⟩).lower ∧ (cell12461 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12461 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12461 ⟨32,by decide⟩).lower ∧ (cell12461 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12461 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12461 ⟨33,by decide⟩).lower ∧ (cell12461 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12461 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12461 ⟨34,by decide⟩).lower ∧ (cell12461 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12461 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12461 ⟨35,by decide⟩).lower ∧ (cell12461 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12461 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12461 ⟨36,by decide⟩).lower ∧ (cell12461 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12461 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12461 ⟨37,by decide⟩).lower ∧ (cell12461 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12461 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12461 ⟨38,by decide⟩).lower ∧ (cell12461 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12461 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12461 ⟨39,by decide⟩).lower ∧ (cell12461 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12461 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12461 ⟨40,by decide⟩).lower ∧ (cell12461 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12461 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12461 ⟨41,by decide⟩).lower ∧ (cell12461 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12461 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12461 ⟨42,by decide⟩).lower ∧ (cell12461 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12461 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12461 ⟨43,by decide⟩).lower ∧ (cell12461 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12461 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12461 ⟨44,by decide⟩).lower ∧ (cell12461 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12461 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12461 ⟨45,by decide⟩).lower ∧ (cell12461 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12461 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12461 ⟨46,by decide⟩).lower ∧ (cell12461 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12461 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12461 ⟨47,by decide⟩).lower ∧ (cell12461 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12461 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12461 ⟨48,by decide⟩).lower ∧ (cell12461 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12461 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12461 ⟨49,by decide⟩).lower ∧ (cell12461 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12461 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12461 ⟨50,by decide⟩).lower ∧ (cell12461 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12461 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12461 ⟨51,by decide⟩).lower ∧ (cell12461 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12461 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12461 ⟨52,by decide⟩).lower ∧ (cell12461 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12461 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12461 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12461 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12461,cell12461,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12461 i).lower ∧
    (cell12461 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12461 i).upper ≤ (0.532 : ℝ) ∧
    (cell12461 i).centre ≤ (0.1 : ℝ) ∧ (cell12461 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12461 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12461 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12461

/-! The local source numeric instances at 12461 have no network premises. -/
namespace BstLean.Part269.N12461
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12461)
open BstLean.Part268 (cell12461)

noncomputable def sourceNumerics12461 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12461 (cell12461 i)
      scalarRow12461.M scalarRow12461.H scalarRow12461.xi := by
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
    energy_allowance := scalarRow12461.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12461]
    centre_nonneg := (scalarRow12461.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12461])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12461
/-! Actual 12462 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12462
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12462 ≤ (1.036152568884 : ℝ) := by
  have hr : (111.633328356723 : ℝ) ≤ √(12462 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.633328356723 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12462 12462 (11 / 1000) ≤
    (0.008562739402 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12462) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.633328356723 : ℝ) ≤ √(12462 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12462)
  have hdiv : K / √(12462 : ℝ) ≤ K / 111.633328356723 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.633328356723 ≤ (0.008562739402 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12462.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12462 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12462 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12462 := gPlus_lower 12462
end BstLean.Part269.N12462

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12462
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036152568883 : ℝ) ≤ wn 12462 := by
  have hn : √(12462 : ℝ) ≤ 111.633328356724 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12462 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.633328356724 ≤ 2 / √(12462 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256776392 : ℝ) ≤ rhoBar 12462 BstLean.Part154.csC ∧
    rhoBar 12462 BstLean.Part154.csC ≤ 0.000256776789 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036152568883 : ℝ) / (1.295212 * 12462) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036152568884 : ℝ) / (1.29521 * 12462) := by gcongr
      _ ≤ (0.000256776789 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12462 BstLean.Part154.csC) ≤ 0.001027173091 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12462 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12462 BstLean.Part154.csC) (piBar (rhoBar 12462 BstLean.Part154.csC)) ≤ 0.000196128021 ∧
    cc1 (rhoBar 12462 BstLean.Part154.csC) (piBar (rhoBar 12462 BstLean.Part154.csC)) ≤ 0.000124797526 ∧
    cc2 (rhoBar 12462 BstLean.Part154.csC) ≤ 0.000072445875 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12462 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12462 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12462 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12462 BstLean.Part154.csC * nuR (rhoBar 12462 BstLean.Part154.csC)) ≤ 0.000513570062 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256776789 : ℝ) * 0.001027173091 := by gcongr
      _ ≤ (0.000513570062 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12462 BstLean.Part154.csC) * nuR (rhoBar 12462 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001027173091 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12462 BstLean.Part154.csC) * rhoBar 12462 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256776789 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256776789 / 2 + 0.399 * 0.001027173091 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196128021 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513570062 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124797526 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256776789 / 1.414213562 := by gcongr
      _ ≤ (0.000072445875 : ℝ) := by norm_num

end BstLean.Part269.N12462

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12462
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12462 BstLean.Part154.csC) (piBar (rhoBar 12462 BstLean.Part154.csC)) ≤ 1.66117E-7 := by
  have hr0 : 0 ≤ rhoBar 12462 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12462 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12462 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12462 BstLean.Part154.csC) (piBar (rhoBar 12462 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12462 BstLean.Part154.csC) (piBar (rhoBar 12462 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12462 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196128021 : ℝ) ^ 2 + 0.000124797526 ^ 2 + 3 * 0.000072445875 ^ 2 +
        2 * 0.797885 * 0.000196128021 * 0.000124797526 + 2 * 0.000196128021 * 0.000072445875 +
        4 * 0.797885 * 0.000124797526 * 0.000072445875 := by gcongr
    _ ≤ (1.66117E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12462 BstLean.Part154.csC Θ ≤ 0.002681283197 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12462 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12462 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12462 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12462 BstLean.Part154.csC) (piBar (rhoBar 12462 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12462 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036152568884 * 1.66117E-7 / (0.000256776392 : ℝ) := by gcongr
    _ ≤ 0.002681283197 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12462 BstLean.Part154.csC Θ ≤ 0.002976014619 + 0.000677516189 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12462 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12462 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12462 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036152568884 : ℝ) * ((2 * Θ * 0.000256776789 +
        (6863 / 10000) * 0.000256776789 * 12462 * 0.001027173091) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002976014619 + 0.000677516189 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12462 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12462 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12462 0.011 Θ ∧ gammaRatio 12462 0.011 Θ ≤ 0.000088273220 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12462 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036152568884 : ℝ) * 0.525 / ((1 - 0.011) * 12462) := by gcongr
      _ ≤ (0.000088273220 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12462 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12462 0.011 Θ) :=
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
    badAllowance 12462 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000816374746 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12462 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12462 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12462 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12462 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12462 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12462 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12462 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12462 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12462 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12462 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036152568884 : ℝ) * 12462 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000816374746 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12462 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003792389365 + 0.003358799386 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12462

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12462
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12462 BstLean.Part154.csC) (piBar (rhoBar 12462 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12462 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12462 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12462 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12462 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12462 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12462 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12462 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12462 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12462 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12462 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12462 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12462 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12462 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12462 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052988576909 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12462) ≤ 0.010697858773 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12462 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036152568884)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010697858773 + 2 * 0.737676 / 12462) := by gcongr
    _ ≤ (0.052988576909 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12462 12 ≤ 0.0015 := by
  exact BstLean.Part269.S4.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12462

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12462
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560492599670 : ℝ) ≤ plow 12462 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12462) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053062359043)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407673679) : eMP 12462 0.011 xi bn ≤ 0.001211545097 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12462 : ℝ) * (1 - 0.011))) ≤ 0.000599009812 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001407673679 / (12462 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000599009812 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000599009812 : ℝ) + 3.141593 * 0.053062359043 / (12462 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001211545097 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053062359043)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407673679) : PiBarMP 12462 12 0.011 xi bn ≤ 0.162799377216 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12462 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037518977585 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.017647245832 : ℝ) ≤ √((12462 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.633328356723 : ℝ) ≤ √(12462 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12462) ≤ 0.124805096004 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037518977585 + 0.053062359043 * 1.772454 / (2 * (111.017647245832 : ℝ))) * (1 + 0.001211545097) +
        8 / (12462 * 111.633328356723) + 0.124805096004 := by gcongr
    _ ≤ (0.162799377216 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053062359043)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407673679) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283341260946) :
    parallelOracle 12462 0.011 xi bn cd ≤ 0.163809531837 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12462 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12462 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560492599670 : ℝ) ≤ plow 12462 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.633328356723 : ℝ) ≤ √(12462 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283341260946 : ℝ) / (2 * 0.560492599670 * 111.633328356723)) * 0.162799377216 +
        0.283341260946 ^ 2 / (2 * 0.560492599670 * 111.633328356723) := by gcongr
    _ ≤ (0.163809531837 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053062359043) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001407673679)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283341260946) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12462 12462 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560492599670 : ℝ) ≤ plow 12462 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.633328356723 : ℝ) ≤ √(12462 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12462 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12462 Θ 1.22 ≤ 0.011879073388 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.633328356723 := by gcongr <;> linarith
      _ ≤ (0.011879073388 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12462 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12462 12462 0.011 ≤ 0.008562739402 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12462 12462 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12462 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12462 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12462 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12462 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163809531837 + 0.011879073388 + (0.008562739402 : ℝ) *
        (1 + 2 * (0.283341260946 + 0.011879073388) / (0.560492599670 * 111.633328356723))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12462]

end BstLean.Part269.N12462

/-! The original eight local profiles supply actual 12462 moment certificates. -/
namespace BstLean.Part269.N12462
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12462 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12462 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12462 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053062359043 ∧
    0 ≤ bN 12462 BstLean.Part154.csC (groupTheta g) ∧ bN 12462 BstLean.Part154.csC (groupTheta g) ≤ 0.001407673679 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12462 12462 0.011
      (momentAllowance 12462 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12462 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12462 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12462 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12462 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12462 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230352684037 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12462 0.011
      (momentAllowance 12462 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12462 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12462
/-! The actual computed-centre upper energy formula at 12462. -/
namespace BstLean.Part269.N12462
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12462

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12462
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12462)
open BstLean.Part268 (cell12462)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086217702754
  | 2 => 0.087174604612
  | 3 => 0.088131834990
  | 4 => 0.089091306560
  | 5 => 0.090055314789
  | 6 => 0.091026592413
  | 7 => 0.092008368586
  | 8 => 0.093004432698
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12462 12462 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12462 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12462

/-! Actual upper energy certificates on all 43 source endpoints at 12462. -/
namespace BstLean.Part269.N12462
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12462)
open BstLean.Part268 (cell12462)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12462 (gMinus 12462) (1 - (cell12462 i).lower) ≤ 1 ∧
    energyUpper 12462 (gMinus 12462) (BstLean.Part211.gPlus 12462)
      (finiteEnergy 12462 12462 0.011) (1 - (cell12462 i).lower) ≤
      (cell12462 i).energy := by
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
      have E := BstLean.Part269.S4.uniformEnergy10 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨10,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy11 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨11,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy12 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨12,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy13 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨13,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy14 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨14,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy15 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨15,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy16 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨16,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy17 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨17,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy18 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨18,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy19 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨19,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy20 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨20,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy21 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨21,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy22 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨22,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy23 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨23,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy24 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨24,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy25 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨25,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy26 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨26,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy27 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨27,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy28 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨28,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy29 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨29,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy30 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨30,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy31 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨31,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy32 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨32,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy33 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨33,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy34 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨34,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy35 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨35,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy36 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨36,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy37 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨37,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy38 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨38,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy39 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨39,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy40 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨40,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy41 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨41,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy42 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨42,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy43 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨43,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy44 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨44,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy45 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨45,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy46 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨46,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy47 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨47,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy48 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨48,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy49 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨49,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy50 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨50,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy51 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨51,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S4.uniformEnergy52 (n := 12462) (by norm_num)
        (q := 1 - (cell12462 ⟨52,by decide⟩).lower)
        (by norm_num [cell12462]) (by norm_num [cell12462])
      exact ⟨E.1,E.2.trans (by norm_num [cell12462])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12462

/-! Source-cell containment and simple scalar guards at 12462. -/
namespace BstLean.Part269.N12462
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12462)
open BstLean.Part268 (cell12462)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12462 ⟨10,by decide⟩).lower ∧ (cell12462 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12462 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12462 ⟨11,by decide⟩).lower ∧ (cell12462 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12462 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12462 ⟨12,by decide⟩).lower ∧ (cell12462 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12462 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12462 ⟨13,by decide⟩).lower ∧ (cell12462 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12462 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12462 ⟨14,by decide⟩).lower ∧ (cell12462 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12462 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12462 ⟨15,by decide⟩).lower ∧ (cell12462 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12462 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12462 ⟨16,by decide⟩).lower ∧ (cell12462 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12462 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12462 ⟨17,by decide⟩).lower ∧ (cell12462 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12462 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12462 ⟨18,by decide⟩).lower ∧ (cell12462 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12462 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12462 ⟨19,by decide⟩).lower ∧ (cell12462 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12462 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12462 ⟨20,by decide⟩).lower ∧ (cell12462 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12462 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12462 ⟨21,by decide⟩).lower ∧ (cell12462 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12462 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12462 ⟨22,by decide⟩).lower ∧ (cell12462 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12462 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12462 ⟨23,by decide⟩).lower ∧ (cell12462 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12462 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12462 ⟨24,by decide⟩).lower ∧ (cell12462 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12462 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12462 ⟨25,by decide⟩).lower ∧ (cell12462 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12462 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12462 ⟨26,by decide⟩).lower ∧ (cell12462 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12462 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12462 ⟨27,by decide⟩).lower ∧ (cell12462 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12462 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12462 ⟨28,by decide⟩).lower ∧ (cell12462 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12462 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12462 ⟨29,by decide⟩).lower ∧ (cell12462 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12462 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12462 ⟨30,by decide⟩).lower ∧ (cell12462 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12462 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12462 ⟨31,by decide⟩).lower ∧ (cell12462 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12462 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12462 ⟨32,by decide⟩).lower ∧ (cell12462 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12462 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12462 ⟨33,by decide⟩).lower ∧ (cell12462 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12462 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12462 ⟨34,by decide⟩).lower ∧ (cell12462 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12462 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12462 ⟨35,by decide⟩).lower ∧ (cell12462 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12462 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12462 ⟨36,by decide⟩).lower ∧ (cell12462 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12462 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12462 ⟨37,by decide⟩).lower ∧ (cell12462 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12462 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12462 ⟨38,by decide⟩).lower ∧ (cell12462 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12462 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12462 ⟨39,by decide⟩).lower ∧ (cell12462 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12462 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12462 ⟨40,by decide⟩).lower ∧ (cell12462 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12462 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12462 ⟨41,by decide⟩).lower ∧ (cell12462 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12462 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12462 ⟨42,by decide⟩).lower ∧ (cell12462 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12462 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12462 ⟨43,by decide⟩).lower ∧ (cell12462 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12462 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12462 ⟨44,by decide⟩).lower ∧ (cell12462 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12462 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12462 ⟨45,by decide⟩).lower ∧ (cell12462 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12462 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12462 ⟨46,by decide⟩).lower ∧ (cell12462 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12462 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12462 ⟨47,by decide⟩).lower ∧ (cell12462 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12462 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12462 ⟨48,by decide⟩).lower ∧ (cell12462 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12462 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12462 ⟨49,by decide⟩).lower ∧ (cell12462 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12462 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12462 ⟨50,by decide⟩).lower ∧ (cell12462 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12462 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12462 ⟨51,by decide⟩).lower ∧ (cell12462 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12462 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12462 ⟨52,by decide⟩).lower ∧ (cell12462 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12462 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12462 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12462 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12462,cell12462,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12462 i).lower ∧
    (cell12462 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12462 i).upper ≤ (0.532 : ℝ) ∧
    (cell12462 i).centre ≤ (0.1 : ℝ) ∧ (cell12462 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12462 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12462 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12462

/-! The local source numeric instances at 12462 have no network premises. -/
namespace BstLean.Part269.N12462
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12462)
open BstLean.Part268 (cell12462)

noncomputable def sourceNumerics12462 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12462 (cell12462 i)
      scalarRow12462.M scalarRow12462.H scalarRow12462.xi := by
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
    energy_allowance := scalarRow12462.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12462]
    centre_nonneg := (scalarRow12462.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D4.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12462])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12462