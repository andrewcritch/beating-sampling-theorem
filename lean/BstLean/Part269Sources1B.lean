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
import BstLean.Part269Direction1
import BstLean.Part269Shared1
import BstLean.Part269Finite
import BstLean.Part269Rows1
import BstLean.Part269Source
/-! Actual 12388 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12388
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12388 ≤ (1.036261347312 : ℝ) := by
  have hr : (111.301392623812 : ℝ) ≤ √(12388 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.301392623812 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12388 12388 (11 / 1000) ≤
    (0.008588276383 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12388) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.301392623812 : ℝ) ≤ √(12388 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12388)
  have hdiv : K / √(12388 : ℝ) ≤ K / 111.301392623812 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.301392623812 ≤ (0.008588276383 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12388.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12388 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12388 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12388 := gPlus_lower 12388
end BstLean.Part269.N12388

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12388
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036261347311 : ℝ) ≤ wn 12388 := by
  have hn : √(12388 : ℝ) ≤ 111.301392623813 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12388 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.301392623813 ≤ 2 / √(12388 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258337370 : ℝ) ≤ rhoBar 12388 BstLean.Part154.csC ∧
    rhoBar 12388 BstLean.Part154.csC ≤ 0.000258337770 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036261347311 : ℝ) / (1.295212 * 12388) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036261347312 : ℝ) / (1.29521 * 12388) := by gcongr
      _ ≤ (0.000258337770 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12388 BstLean.Part154.csC) ≤ 0.001033417819 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12388 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12388 BstLean.Part154.csC) (piBar (rhoBar 12388 BstLean.Part154.csC)) ≤ 0.000197320367 ∧
    cc1 (rhoBar 12388 BstLean.Part154.csC) (piBar (rhoBar 12388 BstLean.Part154.csC)) ≤ 0.000125556211 ∧
    cc2 (rhoBar 12388 BstLean.Part154.csC) ≤ 0.000072886284 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12388 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12388 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12388 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12388 BstLean.Part154.csC * nuR (rhoBar 12388 BstLean.Part154.csC)) ≤ 0.000516692225 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258337770 : ℝ) * 0.001033417819 := by gcongr
      _ ≤ (0.000516692225 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12388 BstLean.Part154.csC) * nuR (rhoBar 12388 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001033417819 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12388 BstLean.Part154.csC) * rhoBar 12388 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258337770 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258337770 / 2 + 0.399 * 0.001033417819 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197320367 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516692225 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125556211 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258337770 / 1.414213562 := by gcongr
      _ ≤ (0.000072886284 : ℝ) := by norm_num

end BstLean.Part269.N12388

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12388
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12388 BstLean.Part154.csC) (piBar (rhoBar 12388 BstLean.Part154.csC)) ≤ 1.68143E-7 := by
  have hr0 : 0 ≤ rhoBar 12388 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12388 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12388 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12388 BstLean.Part154.csC) (piBar (rhoBar 12388 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12388 BstLean.Part154.csC) (piBar (rhoBar 12388 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12388 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197320367 : ℝ) ^ 2 + 0.000125556211 ^ 2 + 3 * 0.000072886284 ^ 2 +
        2 * 0.797885 * 0.000197320367 * 0.000125556211 + 2 * 0.000197320367 * 0.000072886284 +
        4 * 0.797885 * 0.000125556211 * 0.000072886284 := by gcongr
    _ ≤ (1.68143E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12388 BstLean.Part154.csC Θ ≤ 0.002697868942 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12388 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12388 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12388 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12388 BstLean.Part154.csC) (piBar (rhoBar 12388 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12388 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036261347312 * 1.68143E-7 / (0.000258337370 : ℝ) := by gcongr
    _ ≤ 0.002697868942 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12388 BstLean.Part154.csC Θ ≤ 0.002994736087 + 0.000681706462 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12388 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12388 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12388 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036261347312 : ℝ) * ((2 * Θ * 0.000258337770 +
        (6863 / 10000) * 0.000258337770 * 12388 * 0.001033417819) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002994736087 + 0.000681706462 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12388 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12388 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12388 0.011 Θ ∧ gammaRatio 12388 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12388 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036261347312 : ℝ) * 0.525 / ((1 - 0.011) * 12388) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12388 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12388 0.011 Θ) :=
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
    badAllowance 12388 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12388 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12388 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12388 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12388 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12388 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12388 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12388 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12388 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12388 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12388 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036261347312 : ℝ) * 12388 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12388 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004094736087 + 0.003379575404 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12388

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12388
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12388 BstLean.Part154.csC) (piBar (rhoBar 12388 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12388 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12388 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12388 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12388 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12388 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12388 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12388 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12388 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12388 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12388 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12388 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12388 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12388 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12388 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053148340342 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12388) ≤ 0.010729763150 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12388 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036261347312)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010729763150 + 2 * 0.737676 / 12388) := by gcongr
    _ ≤ (0.053148340342 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12388 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12388

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12388
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489103366 : ℝ) ≤ plow 12388 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12388) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053375613175)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416381195) : eMP 12388 0.011 xi bn ≤ 0.001218989732 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12388 : ℝ) * (1 - 0.011))) ≤ 0.000602651570 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001416381195 / (12388 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602651570 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602651570 : ℝ) + 3.141593 * 0.053375613175 / (12388 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001218989732 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053375613175)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416381195) : PiBarMP 12388 12 0.011 xi bn ≤ 0.163291699081 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12388 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037634840176 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.687542207784 : ℝ) ≤ √((12388 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.301392623812 : ℝ) ≤ √(12388 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12388) ≤ 0.125177304024 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037634840176 + 0.053375613175 * 1.772454 / (2 * (110.687542207784 : ℝ))) * (1 + 0.001218989732) +
        8 / (12388 * 111.301392623812) + 0.125177304024 := by gcongr
    _ ≤ (0.163291699081 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053375613175)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416381195) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284179968426) :
    parallelOracle 12388 0.011 xi bn cd ≤ 0.164310903356 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12388 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12388 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489103366 : ℝ) ≤ plow 12388 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.301392623812 : ℝ) ≤ √(12388 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284179968426 : ℝ) / (2 * 0.560489103366 * 111.301392623812)) * 0.163291699081 +
        0.284179968426 ^ 2 / (2 * 0.560489103366 * 111.301392623812) := by gcongr
    _ ≤ (0.164310903356 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053375613175) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416381195)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284179968426) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12388 12388 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489103366 : ℝ) ≤ plow 12388 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.301392623812 : ℝ) ≤ √(12388 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12388 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12388 Θ 1.22 ≤ 0.011914500518 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.301392623812 := by gcongr <;> linarith
      _ ≤ (0.011914500518 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12388 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12388 12388 0.011 ≤ 0.008588276383 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12388 12388 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12388 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12388 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12388 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12388 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164310903356 + 0.011914500518 + (0.008588276383 : ℝ) *
        (1 + 2 * (0.284179968426 + 0.011914500518) / (0.560489103366 * 111.301392623812))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12388]

end BstLean.Part269.N12388

/-! The original eight local profiles supply actual 12388 moment certificates. -/
namespace BstLean.Part269.N12388
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12388 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12388 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12388 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053375613175 ∧
    0 ≤ bN 12388 BstLean.Part154.csC (groupTheta g) ∧ bN 12388 BstLean.Part154.csC (groupTheta g) ≤ 0.001416381195 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12388 12388 0.011
      (momentAllowance 12388 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12388 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12388 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12388 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12388 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12388 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231031628084 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12388 0.011
      (momentAllowance 12388 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12388 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12388
/-! The actual computed-centre upper energy formula at 12388. -/
namespace BstLean.Part269.N12388
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12388

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12388
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12388)
open BstLean.Part268 (cell12388)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086459064768
  | 2 => 0.087421021809
  | 3 => 0.088384141070
  | 4 => 0.089350519339
  | 5 => 0.090322667326
  | 6 => 0.091303567735
  | 7 => 0.092296738186
  | 8 => 0.093306298935
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12388 12388 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12388 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004098049004 + 0.003383255859 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S1.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12388

/-! Actual upper energy certificates on all 43 source endpoints at 12388. -/
namespace BstLean.Part269.N12388
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12388)
open BstLean.Part268 (cell12388)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12388 (gMinus 12388) (1 - (cell12388 i).lower) ≤ 1 ∧
    energyUpper 12388 (gMinus 12388) (BstLean.Part211.gPlus 12388)
      (finiteEnergy 12388 12388 0.011) (1 - (cell12388 i).lower) ≤
      (cell12388 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨10,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨11,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨12,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨13,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨14,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨15,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨16,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨17,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨18,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨19,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨20,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨21,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨22,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨23,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨24,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨25,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨26,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨27,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨28,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨29,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨30,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨31,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨32,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨33,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨34,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨35,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨36,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨37,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨38,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨39,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨40,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨41,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨42,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨43,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨44,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨45,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨46,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨47,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨48,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨49,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨50,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨51,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12388) (by norm_num)
        (q := 1 - (cell12388 ⟨52,by decide⟩).lower)
        (by norm_num [cell12388]) (by norm_num [cell12388])
      exact ⟨E.1,E.2.trans (by norm_num [cell12388])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12388

/-! Source-cell containment and simple scalar guards at 12388. -/
namespace BstLean.Part269.N12388
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12388)
open BstLean.Part268 (cell12388)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12388 ⟨10,by decide⟩).lower ∧ (cell12388 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12388 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12388 ⟨11,by decide⟩).lower ∧ (cell12388 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12388 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12388 ⟨12,by decide⟩).lower ∧ (cell12388 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12388 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12388 ⟨13,by decide⟩).lower ∧ (cell12388 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12388 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12388 ⟨14,by decide⟩).lower ∧ (cell12388 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12388 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12388 ⟨15,by decide⟩).lower ∧ (cell12388 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12388 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12388 ⟨16,by decide⟩).lower ∧ (cell12388 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12388 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12388 ⟨17,by decide⟩).lower ∧ (cell12388 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12388 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12388 ⟨18,by decide⟩).lower ∧ (cell12388 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12388 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12388 ⟨19,by decide⟩).lower ∧ (cell12388 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12388 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12388 ⟨20,by decide⟩).lower ∧ (cell12388 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12388 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12388 ⟨21,by decide⟩).lower ∧ (cell12388 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12388 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12388 ⟨22,by decide⟩).lower ∧ (cell12388 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12388 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12388 ⟨23,by decide⟩).lower ∧ (cell12388 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12388 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12388 ⟨24,by decide⟩).lower ∧ (cell12388 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12388 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12388 ⟨25,by decide⟩).lower ∧ (cell12388 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12388 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12388 ⟨26,by decide⟩).lower ∧ (cell12388 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12388 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12388 ⟨27,by decide⟩).lower ∧ (cell12388 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12388 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12388 ⟨28,by decide⟩).lower ∧ (cell12388 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12388 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12388 ⟨29,by decide⟩).lower ∧ (cell12388 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12388 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12388 ⟨30,by decide⟩).lower ∧ (cell12388 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12388 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12388 ⟨31,by decide⟩).lower ∧ (cell12388 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12388 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12388 ⟨32,by decide⟩).lower ∧ (cell12388 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12388 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12388 ⟨33,by decide⟩).lower ∧ (cell12388 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12388 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12388 ⟨34,by decide⟩).lower ∧ (cell12388 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12388 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12388 ⟨35,by decide⟩).lower ∧ (cell12388 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12388 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12388 ⟨36,by decide⟩).lower ∧ (cell12388 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12388 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12388 ⟨37,by decide⟩).lower ∧ (cell12388 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12388 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12388 ⟨38,by decide⟩).lower ∧ (cell12388 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12388 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12388 ⟨39,by decide⟩).lower ∧ (cell12388 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12388 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12388 ⟨40,by decide⟩).lower ∧ (cell12388 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12388 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12388 ⟨41,by decide⟩).lower ∧ (cell12388 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12388 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12388 ⟨42,by decide⟩).lower ∧ (cell12388 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12388 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12388 ⟨43,by decide⟩).lower ∧ (cell12388 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12388 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12388 ⟨44,by decide⟩).lower ∧ (cell12388 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12388 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12388 ⟨45,by decide⟩).lower ∧ (cell12388 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12388 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12388 ⟨46,by decide⟩).lower ∧ (cell12388 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12388 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12388 ⟨47,by decide⟩).lower ∧ (cell12388 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12388 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12388 ⟨48,by decide⟩).lower ∧ (cell12388 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12388 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12388 ⟨49,by decide⟩).lower ∧ (cell12388 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12388 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12388 ⟨50,by decide⟩).lower ∧ (cell12388 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12388 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12388 ⟨51,by decide⟩).lower ∧ (cell12388 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12388 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12388 ⟨52,by decide⟩).lower ∧ (cell12388 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12388 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12388 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12388 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12388,cell12388,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12388 i).lower ∧
    (cell12388 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12388 i).upper ≤ (0.532 : ℝ) ∧
    (cell12388 i).centre ≤ (0.1 : ℝ) ∧ (cell12388 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12388 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12388 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12388

/-! The local source numeric instances at 12388 have no network premises. -/
namespace BstLean.Part269.N12388
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12388)
open BstLean.Part268 (cell12388)

noncomputable def sourceNumerics12388 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12388 (cell12388 i)
      scalarRow12388.M scalarRow12388.H scalarRow12388.xi := by
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
    energy_allowance := scalarRow12388.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12388]
    centre_nonneg := (scalarRow12388.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12388])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12388
/-! Actual 12389 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12389
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12389 ≤ (1.036259870802 : ℝ) := by
  have hr : (111.305884839931 : ℝ) ≤ √(12389 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.305884839931 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12389 12389 (11 / 1000) ≤
    (0.008587929764 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12389) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.305884839931 : ℝ) ≤ √(12389 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12389)
  have hdiv : K / √(12389 : ℝ) ≤ K / 111.305884839931 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.305884839931 ≤ (0.008587929764 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12389.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12389 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12389 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12389 := gPlus_lower 12389
end BstLean.Part269.N12389

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12389
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036259870801 : ℝ) ≤ wn 12389 := by
  have hn : √(12389 : ℝ) ≤ 111.305884839932 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12389 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.305884839932 ≤ 2 / √(12389 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258316150 : ℝ) ≤ rhoBar 12389 BstLean.Part154.csC ∧
    rhoBar 12389 BstLean.Part154.csC ≤ 0.000258316549 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036259870801 : ℝ) / (1.295212 * 12389) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036259870802 : ℝ) / (1.29521 * 12389) := by gcongr
      _ ≤ (0.000258316549 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12389 BstLean.Part154.csC) ≤ 0.001033332924 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12389 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12389 BstLean.Part154.csC) (piBar (rhoBar 12389 BstLean.Part154.csC)) ≤ 0.000197304157 ∧
    cc1 (rhoBar 12389 BstLean.Part154.csC) (piBar (rhoBar 12389 BstLean.Part154.csC)) ≤ 0.000125545897 ∧
    cc2 (rhoBar 12389 BstLean.Part154.csC) ≤ 0.000072880297 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12389 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12389 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12389 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12389 BstLean.Part154.csC * nuR (rhoBar 12389 BstLean.Part154.csC)) ≤ 0.000516649780 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258316549 : ℝ) * 0.001033332924 := by gcongr
      _ ≤ (0.000516649780 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12389 BstLean.Part154.csC) * nuR (rhoBar 12389 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001033332924 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12389 BstLean.Part154.csC) * rhoBar 12389 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258316549 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258316549 / 2 + 0.399 * 0.001033332924 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197304157 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516649780 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125545897 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258316549 / 1.414213562 := by gcongr
      _ ≤ (0.000072880297 : ℝ) := by norm_num

end BstLean.Part269.N12389

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12389
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12389 BstLean.Part154.csC) (piBar (rhoBar 12389 BstLean.Part154.csC)) ≤ 1.68115E-7 := by
  have hr0 : 0 ≤ rhoBar 12389 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12389 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12389 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12389 BstLean.Part154.csC) (piBar (rhoBar 12389 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12389 BstLean.Part154.csC) (piBar (rhoBar 12389 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12389 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197304157 : ℝ) ^ 2 + 0.000125545897 ^ 2 + 3 * 0.000072880297 ^ 2 +
        2 * 0.797885 * 0.000197304157 * 0.000125545897 + 2 * 0.000197304157 * 0.000072880297 +
        4 * 0.797885 * 0.000125545897 * 0.000072880297 := by gcongr
    _ ≤ (1.68115E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12389 BstLean.Part154.csC Θ ≤ 0.002697637422 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12389 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12389 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12389 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12389 BstLean.Part154.csC) (piBar (rhoBar 12389 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12389 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036259870802 * 1.68115E-7 / (0.000258316150 : ℝ) := by gcongr
    _ ≤ 0.002697637422 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12389 BstLean.Part154.csC Θ ≤ 0.002994481528 + 0.000681649492 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12389 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12389 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12389 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036259870802 : ℝ) * ((2 * Θ * 0.000258316549 +
        (6863 / 10000) * 0.000258316549 * 12389 * 0.001033332924) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002994481528 + 0.000681649492 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12389 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12389 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12389 0.011 Θ ∧ gammaRatio 12389 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12389 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036259870802 : ℝ) * 0.525 / ((1 - 0.011) * 12389) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12389 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12389 0.011 Θ) :=
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
    badAllowance 12389 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12389 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12389 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12389 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12389 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12389 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12389 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12389 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12389 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12389 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12389 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036259870802 : ℝ) * 12389 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12389 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004094481528 + 0.003379286914 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12389

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12389
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12389 BstLean.Part154.csC) (piBar (rhoBar 12389 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12389 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12389 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12389 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12389 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12389 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12389 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12389 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12389 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12389 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12389 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12389 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12389 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12389 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12389 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053146171769 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12389) ≤ 0.010729330105 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12389 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036259870802)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010729330105 + 2 * 0.737676 / 12389) := by gcongr
    _ ≤ (0.053146171769 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12389 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12389

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12389
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489150891 : ℝ) ≤ plow 12389 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12389) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053375207158)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416259647) : eMP 12389 0.011 xi bn ≤ 0.001218888163 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12389 : ℝ) * (1 - 0.011))) ≤ 0.000602601390 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001416259647 / (12389 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602601390 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602601390 : ℝ) + 3.141593 * 0.053375207158 / (12389 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001218888163 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053375207158)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416259647) : PiBarMP 12389 12 0.011 xi bn ≤ 0.163285005097 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12389 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037633225307 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.692009648393 : ℝ) ≤ √((12389 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.305884839931 : ℝ) ≤ √(12389 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12389) ≤ 0.125172251969 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037633225307 + 0.053375207158 * 1.772454 / (2 * (110.692009648393 : ℝ))) * (1 + 0.001218888163) +
        8 / (12389 * 111.305884839931) + 0.125172251969 := by gcongr
    _ ≤ (0.163285005097 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053375207158)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416259647) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284176921147) :
    parallelOracle 12389 0.011 xi bn cd ≤ 0.164304135036 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12389 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12389 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489150891 : ℝ) ≤ plow 12389 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.305884839931 : ℝ) ≤ √(12389 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284176921147 : ℝ) / (2 * 0.560489150891 * 111.305884839931)) * 0.163285005097 +
        0.284176921147 ^ 2 / (2 * 0.560489150891 * 111.305884839931) := by gcongr
    _ ≤ (0.164304135036 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053375207158) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416259647)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284176921147) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12389 12389 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489150891 : ℝ) ≤ plow 12389 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.305884839931 : ℝ) ≤ √(12389 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12389 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12389 Θ 1.22 ≤ 0.011914019658 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.305884839931 := by gcongr <;> linarith
      _ ≤ (0.011914019658 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12389 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12389 12389 0.011 ≤ 0.008587929764 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12389 12389 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12389 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12389 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12389 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12389 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164304135036 + 0.011914019658 + (0.008587929764 : ℝ) *
        (1 + 2 * (0.284176921147 + 0.011914019658) / (0.560489150891 * 111.305884839931))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12389]

end BstLean.Part269.N12389

/-! The original eight local profiles supply actual 12389 moment certificates. -/
namespace BstLean.Part269.N12389
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12389 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12389 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12389 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053375207158 ∧
    0 ≤ bN 12389 BstLean.Part154.csC (groupTheta g) ∧ bN 12389 BstLean.Part154.csC (groupTheta g) ≤ 0.001416259647 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12389 12389 0.011
      (momentAllowance 12389 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12389 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12389 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12389 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12389 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12389 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231030749378 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12389 0.011
      (momentAllowance 12389 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12389 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12389
/-! The actual computed-centre upper energy formula at 12389. -/
namespace BstLean.Part269.N12389
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12389

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12389
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12389)
open BstLean.Part268 (cell12389)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086455749612
  | 2 => 0.087417635977
  | 3 => 0.088380672744
  | 4 => 0.089346954106
  | 5 => 0.090318987743
  | 6 => 0.091299752839
  | 7 => 0.092292762958
  | 8 => 0.093302133707
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12389 12389 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12389 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004098049004 + 0.003383255859 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S1.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12389

/-! Actual upper energy certificates on all 43 source endpoints at 12389. -/
namespace BstLean.Part269.N12389
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12389)
open BstLean.Part268 (cell12389)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12389 (gMinus 12389) (1 - (cell12389 i).lower) ≤ 1 ∧
    energyUpper 12389 (gMinus 12389) (BstLean.Part211.gPlus 12389)
      (finiteEnergy 12389 12389 0.011) (1 - (cell12389 i).lower) ≤
      (cell12389 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨10,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨11,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨12,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨13,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨14,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨15,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨16,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨17,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨18,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨19,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨20,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨21,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨22,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨23,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨24,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨25,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨26,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨27,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨28,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨29,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨30,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨31,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨32,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨33,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨34,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨35,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨36,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨37,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨38,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨39,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨40,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨41,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨42,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨43,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨44,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨45,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨46,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨47,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨48,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨49,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨50,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨51,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12389) (by norm_num)
        (q := 1 - (cell12389 ⟨52,by decide⟩).lower)
        (by norm_num [cell12389]) (by norm_num [cell12389])
      exact ⟨E.1,E.2.trans (by norm_num [cell12389])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12389

/-! Source-cell containment and simple scalar guards at 12389. -/
namespace BstLean.Part269.N12389
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12389)
open BstLean.Part268 (cell12389)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12389 ⟨10,by decide⟩).lower ∧ (cell12389 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12389 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12389 ⟨11,by decide⟩).lower ∧ (cell12389 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12389 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12389 ⟨12,by decide⟩).lower ∧ (cell12389 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12389 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12389 ⟨13,by decide⟩).lower ∧ (cell12389 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12389 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12389 ⟨14,by decide⟩).lower ∧ (cell12389 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12389 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12389 ⟨15,by decide⟩).lower ∧ (cell12389 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12389 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12389 ⟨16,by decide⟩).lower ∧ (cell12389 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12389 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12389 ⟨17,by decide⟩).lower ∧ (cell12389 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12389 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12389 ⟨18,by decide⟩).lower ∧ (cell12389 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12389 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12389 ⟨19,by decide⟩).lower ∧ (cell12389 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12389 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12389 ⟨20,by decide⟩).lower ∧ (cell12389 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12389 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12389 ⟨21,by decide⟩).lower ∧ (cell12389 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12389 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12389 ⟨22,by decide⟩).lower ∧ (cell12389 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12389 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12389 ⟨23,by decide⟩).lower ∧ (cell12389 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12389 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12389 ⟨24,by decide⟩).lower ∧ (cell12389 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12389 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12389 ⟨25,by decide⟩).lower ∧ (cell12389 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12389 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12389 ⟨26,by decide⟩).lower ∧ (cell12389 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12389 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12389 ⟨27,by decide⟩).lower ∧ (cell12389 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12389 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12389 ⟨28,by decide⟩).lower ∧ (cell12389 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12389 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12389 ⟨29,by decide⟩).lower ∧ (cell12389 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12389 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12389 ⟨30,by decide⟩).lower ∧ (cell12389 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12389 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12389 ⟨31,by decide⟩).lower ∧ (cell12389 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12389 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12389 ⟨32,by decide⟩).lower ∧ (cell12389 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12389 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12389 ⟨33,by decide⟩).lower ∧ (cell12389 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12389 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12389 ⟨34,by decide⟩).lower ∧ (cell12389 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12389 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12389 ⟨35,by decide⟩).lower ∧ (cell12389 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12389 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12389 ⟨36,by decide⟩).lower ∧ (cell12389 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12389 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12389 ⟨37,by decide⟩).lower ∧ (cell12389 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12389 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12389 ⟨38,by decide⟩).lower ∧ (cell12389 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12389 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12389 ⟨39,by decide⟩).lower ∧ (cell12389 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12389 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12389 ⟨40,by decide⟩).lower ∧ (cell12389 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12389 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12389 ⟨41,by decide⟩).lower ∧ (cell12389 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12389 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12389 ⟨42,by decide⟩).lower ∧ (cell12389 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12389 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12389 ⟨43,by decide⟩).lower ∧ (cell12389 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12389 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12389 ⟨44,by decide⟩).lower ∧ (cell12389 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12389 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12389 ⟨45,by decide⟩).lower ∧ (cell12389 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12389 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12389 ⟨46,by decide⟩).lower ∧ (cell12389 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12389 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12389 ⟨47,by decide⟩).lower ∧ (cell12389 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12389 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12389 ⟨48,by decide⟩).lower ∧ (cell12389 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12389 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12389 ⟨49,by decide⟩).lower ∧ (cell12389 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12389 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12389 ⟨50,by decide⟩).lower ∧ (cell12389 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12389 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12389 ⟨51,by decide⟩).lower ∧ (cell12389 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12389 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12389 ⟨52,by decide⟩).lower ∧ (cell12389 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12389 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12389 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12389 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12389,cell12389,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12389 i).lower ∧
    (cell12389 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12389 i).upper ≤ (0.532 : ℝ) ∧
    (cell12389 i).centre ≤ (0.1 : ℝ) ∧ (cell12389 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12389 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12389 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12389

/-! The local source numeric instances at 12389 have no network premises. -/
namespace BstLean.Part269.N12389
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12389)
open BstLean.Part268 (cell12389)

noncomputable def sourceNumerics12389 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12389 (cell12389 i)
      scalarRow12389.M scalarRow12389.H scalarRow12389.xi := by
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
    energy_allowance := scalarRow12389.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12389]
    centre_nonneg := (scalarRow12389.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12389])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12389
/-! Actual 12390 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12390
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12390 ≤ (1.036258394472 : ℝ) := by
  have hr : (111.310376874755 : ℝ) ≤ √(12390 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.310376874755 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12390 12390 (11 / 1000) ≤
    (0.008587583188 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12390) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.310376874755 : ℝ) ≤ √(12390 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12390)
  have hdiv : K / √(12390 : ℝ) ≤ K / 111.310376874755 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.310376874755 ≤ (0.008587583188 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12390.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12390 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12390 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12390 := gPlus_lower 12390
end BstLean.Part269.N12390

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12390
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036258394471 : ℝ) ≤ wn 12390 := by
  have hn : √(12390 : ℝ) ≤ 111.310376874756 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12390 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.310376874756 ≤ 2 / √(12390 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258294933 : ℝ) ≤ rhoBar 12390 BstLean.Part154.csC ∧
    rhoBar 12390 BstLean.Part154.csC ≤ 0.000258295333 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036258394471 : ℝ) / (1.295212 * 12390) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036258394472 : ℝ) / (1.29521 * 12390) := by gcongr
      _ ≤ (0.000258295333 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12390 BstLean.Part154.csC) ≤ 0.001033248049 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12390 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12390 BstLean.Part154.csC) (piBar (rhoBar 12390 BstLean.Part154.csC)) ≤ 0.000197287952 ∧
    cc1 (rhoBar 12390 BstLean.Part154.csC) (piBar (rhoBar 12390 BstLean.Part154.csC)) ≤ 0.000125535585 ∧
    cc2 (rhoBar 12390 BstLean.Part154.csC) ≤ 0.000072874311 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12390 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12390 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12390 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12390 BstLean.Part154.csC * nuR (rhoBar 12390 BstLean.Part154.csC)) ≤ 0.000516607345 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258295333 : ℝ) * 0.001033248049 := by gcongr
      _ ≤ (0.000516607345 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12390 BstLean.Part154.csC) * nuR (rhoBar 12390 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001033248049 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12390 BstLean.Part154.csC) * rhoBar 12390 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258295333 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258295333 / 2 + 0.399 * 0.001033248049 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197287952 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516607345 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125535585 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258295333 / 1.414213562 := by gcongr
      _ ≤ (0.000072874311 : ℝ) := by norm_num

end BstLean.Part269.N12390

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12390
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12390 BstLean.Part154.csC) (piBar (rhoBar 12390 BstLean.Part154.csC)) ≤ 1.68088E-7 := by
  have hr0 : 0 ≤ rhoBar 12390 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12390 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12390 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12390 BstLean.Part154.csC) (piBar (rhoBar 12390 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12390 BstLean.Part154.csC) (piBar (rhoBar 12390 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12390 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197287952 : ℝ) ^ 2 + 0.000125535585 ^ 2 + 3 * 0.000072874311 ^ 2 +
        2 * 0.797885 * 0.000197287952 * 0.000125535585 + 2 * 0.000197287952 * 0.000072874311 +
        4 * 0.797885 * 0.000125535585 * 0.000072874311 := by gcongr
    _ ≤ (1.68088E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12390 BstLean.Part154.csC Θ ≤ 0.002697421882 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12390 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12390 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12390 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12390 BstLean.Part154.csC) (piBar (rhoBar 12390 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12390 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036258394472 * 1.68088E-7 / (0.000258294933 : ℝ) := by gcongr
    _ ≤ 0.002697421882 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12390 BstLean.Part154.csC Θ ≤ 0.002994227048 + 0.000681592536 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12390 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12390 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12390 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036258394472 : ℝ) * ((2 * Θ * 0.000258295333 +
        (6863 / 10000) * 0.000258295333 * 12390 * 0.001033248049) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002994227048 + 0.000681592536 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12390 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12390 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12390 0.011 Θ ∧ gammaRatio 12390 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12390 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036258394472 : ℝ) * 0.525 / ((1 - 0.011) * 12390) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12390 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12390 0.011 Θ) :=
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
    badAllowance 12390 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12390 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12390 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12390 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12390 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12390 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12390 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12390 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12390 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12390 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12390 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036258394472 : ℝ) * 12390 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12390 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004094227048 + 0.003379014418 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12390

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12390
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12390 BstLean.Part154.csC) (piBar (rhoBar 12390 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12390 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12390 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12390 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12390 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12390 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12390 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12390 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12390 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12390 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12390 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12390 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12390 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12390 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12390 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053144003464 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12390) ≤ 0.010728897113 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12390 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036258394472)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010728897113 + 2 * 0.737676 / 12390) := by gcongr
    _ ≤ (0.053144003464 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12390 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12390

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12390
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489198410 : ℝ) ≤ plow 12390 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12390) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053374809618)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416146489) : eMP 12390 0.011 xi bn ≤ 0.001218790173 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12390 : ℝ) * (1 - 0.011))) ≤ 0.000602552998 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001416146489 / (12390 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602552998 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602552998 : ℝ) + 3.141593 * 0.053374809618 / (12390 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001218790173 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053374809618)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416146489) : PiBarMP 12390 12 0.011 xi bn ≤ 0.163278423474 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12390 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037631721845 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.696476908707 : ℝ) ≤ √((12390 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.310376874755 : ℝ) ≤ √(12390 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12390) ≤ 0.125167200525 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037631721845 + 0.053374809618 * 1.772454 / (2 * (110.696476908707 : ℝ))) * (1 + 0.001218790173) +
        8 / (12390 * 111.310376874755) + 0.125167200525 := by gcongr
    _ ≤ (0.163278423474 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053374809618)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416146489) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284173892479) :
    parallelOracle 12390 0.011 xi bn cd ≤ 0.164297479450 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12390 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12390 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489198410 : ℝ) ≤ plow 12390 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.310376874755 : ℝ) ≤ √(12390 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284173892479 : ℝ) / (2 * 0.560489198410 * 111.310376874755)) * 0.163278423474 +
        0.284173892479 ^ 2 / (2 * 0.560489198410 * 111.310376874755) := by gcongr
    _ ≤ (0.164297479450 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053374809618) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416146489)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284173892479) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12390 12390 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489198410 : ℝ) ≤ plow 12390 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.310376874755 : ℝ) ≤ √(12390 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12390 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12390 Θ 1.22 ≤ 0.011913538857 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.310376874755 := by gcongr <;> linarith
      _ ≤ (0.011913538857 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12390 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12390 12390 0.011 ≤ 0.008587583188 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12390 12390 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12390 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12390 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12390 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12390 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164297479450 + 0.011913538857 + (0.008587583188 : ℝ) *
        (1 + 2 * (0.284173892479 + 0.011913538857) / (0.560489198410 * 111.310376874755))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12390]

end BstLean.Part269.N12390

/-! The original eight local profiles supply actual 12390 moment certificates. -/
namespace BstLean.Part269.N12390
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12390 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12390 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12390 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053374809618 ∧
    0 ≤ bN 12390 BstLean.Part154.csC (groupTheta g) ∧ bN 12390 BstLean.Part154.csC (groupTheta g) ≤ 0.001416146489 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12390 12390 0.011
      (momentAllowance 12390 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12390 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12390 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12390 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12390 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12390 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231029889015 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12390 0.011
      (momentAllowance 12390 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12390 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12390
/-! The actual computed-centre upper energy formula at 12390. -/
namespace BstLean.Part269.N12390
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12390

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12390
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12390)
open BstLean.Part268 (cell12390)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086452435961
  | 2 => 0.087414251716
  | 3 => 0.088377206071
  | 4 => 0.089343390629
  | 5 => 0.090315310038
  | 6 => 0.091295939970
  | 7 => 0.092288789936
  | 8 => 0.093297970899
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12390 12390 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12390 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004098049004 + 0.003383255859 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S1.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12390

/-! Actual upper energy certificates on all 43 source endpoints at 12390. -/
namespace BstLean.Part269.N12390
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12390)
open BstLean.Part268 (cell12390)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12390 (gMinus 12390) (1 - (cell12390 i).lower) ≤ 1 ∧
    energyUpper 12390 (gMinus 12390) (BstLean.Part211.gPlus 12390)
      (finiteEnergy 12390 12390 0.011) (1 - (cell12390 i).lower) ≤
      (cell12390 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨10,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨11,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨12,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨13,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨14,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨15,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨16,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨17,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨18,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨19,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨20,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨21,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨22,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨23,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨24,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨25,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨26,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨27,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨28,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨29,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨30,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨31,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨32,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨33,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨34,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨35,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨36,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨37,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨38,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨39,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨40,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨41,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨42,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨43,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨44,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨45,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨46,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨47,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨48,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨49,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨50,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨51,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12390) (by norm_num)
        (q := 1 - (cell12390 ⟨52,by decide⟩).lower)
        (by norm_num [cell12390]) (by norm_num [cell12390])
      exact ⟨E.1,E.2.trans (by norm_num [cell12390])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12390

/-! Source-cell containment and simple scalar guards at 12390. -/
namespace BstLean.Part269.N12390
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12390)
open BstLean.Part268 (cell12390)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12390 ⟨10,by decide⟩).lower ∧ (cell12390 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12390 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12390 ⟨11,by decide⟩).lower ∧ (cell12390 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12390 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12390 ⟨12,by decide⟩).lower ∧ (cell12390 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12390 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12390 ⟨13,by decide⟩).lower ∧ (cell12390 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12390 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12390 ⟨14,by decide⟩).lower ∧ (cell12390 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12390 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12390 ⟨15,by decide⟩).lower ∧ (cell12390 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12390 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12390 ⟨16,by decide⟩).lower ∧ (cell12390 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12390 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12390 ⟨17,by decide⟩).lower ∧ (cell12390 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12390 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12390 ⟨18,by decide⟩).lower ∧ (cell12390 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12390 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12390 ⟨19,by decide⟩).lower ∧ (cell12390 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12390 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12390 ⟨20,by decide⟩).lower ∧ (cell12390 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12390 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12390 ⟨21,by decide⟩).lower ∧ (cell12390 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12390 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12390 ⟨22,by decide⟩).lower ∧ (cell12390 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12390 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12390 ⟨23,by decide⟩).lower ∧ (cell12390 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12390 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12390 ⟨24,by decide⟩).lower ∧ (cell12390 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12390 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12390 ⟨25,by decide⟩).lower ∧ (cell12390 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12390 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12390 ⟨26,by decide⟩).lower ∧ (cell12390 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12390 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12390 ⟨27,by decide⟩).lower ∧ (cell12390 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12390 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12390 ⟨28,by decide⟩).lower ∧ (cell12390 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12390 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12390 ⟨29,by decide⟩).lower ∧ (cell12390 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12390 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12390 ⟨30,by decide⟩).lower ∧ (cell12390 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12390 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12390 ⟨31,by decide⟩).lower ∧ (cell12390 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12390 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12390 ⟨32,by decide⟩).lower ∧ (cell12390 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12390 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12390 ⟨33,by decide⟩).lower ∧ (cell12390 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12390 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12390 ⟨34,by decide⟩).lower ∧ (cell12390 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12390 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12390 ⟨35,by decide⟩).lower ∧ (cell12390 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12390 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12390 ⟨36,by decide⟩).lower ∧ (cell12390 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12390 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12390 ⟨37,by decide⟩).lower ∧ (cell12390 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12390 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12390 ⟨38,by decide⟩).lower ∧ (cell12390 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12390 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12390 ⟨39,by decide⟩).lower ∧ (cell12390 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12390 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12390 ⟨40,by decide⟩).lower ∧ (cell12390 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12390 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12390 ⟨41,by decide⟩).lower ∧ (cell12390 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12390 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12390 ⟨42,by decide⟩).lower ∧ (cell12390 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12390 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12390 ⟨43,by decide⟩).lower ∧ (cell12390 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12390 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12390 ⟨44,by decide⟩).lower ∧ (cell12390 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12390 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12390 ⟨45,by decide⟩).lower ∧ (cell12390 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12390 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12390 ⟨46,by decide⟩).lower ∧ (cell12390 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12390 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12390 ⟨47,by decide⟩).lower ∧ (cell12390 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12390 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12390 ⟨48,by decide⟩).lower ∧ (cell12390 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12390 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12390 ⟨49,by decide⟩).lower ∧ (cell12390 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12390 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12390 ⟨50,by decide⟩).lower ∧ (cell12390 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12390 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12390 ⟨51,by decide⟩).lower ∧ (cell12390 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12390 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12390 ⟨52,by decide⟩).lower ∧ (cell12390 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12390 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12390 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12390 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12390,cell12390,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12390 i).lower ∧
    (cell12390 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12390 i).upper ≤ (0.532 : ℝ) ∧
    (cell12390 i).centre ≤ (0.1 : ℝ) ∧ (cell12390 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12390 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12390 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12390

/-! The local source numeric instances at 12390 have no network premises. -/
namespace BstLean.Part269.N12390
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12390)
open BstLean.Part268 (cell12390)

noncomputable def sourceNumerics12390 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12390 (cell12390 i)
      scalarRow12390.M scalarRow12390.H scalarRow12390.xi := by
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
    energy_allowance := scalarRow12390.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12390]
    centre_nonneg := (scalarRow12390.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12390])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12390
/-! Actual 12391 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12391
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12391 ≤ (1.036256918321 : ℝ) := by
  have hr : (111.314868728306 : ℝ) ≤ √(12391 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.314868728306 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12391 12391 (11 / 1000) ≤
    (0.008587236653 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12391) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.314868728306 : ℝ) ≤ √(12391 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12391)
  have hdiv : K / √(12391 : ℝ) ≤ K / 111.314868728306 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.314868728306 ≤ (0.008587236653 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12391.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12391 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12391 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12391 := gPlus_lower 12391
end BstLean.Part269.N12391

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12391
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036256918320 : ℝ) ≤ wn 12391 := by
  have hn : √(12391 : ℝ) ≤ 111.314868728307 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12391 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.314868728307 ≤ 2 / √(12391 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258273720 : ℝ) ≤ rhoBar 12391 BstLean.Part154.csC ∧
    rhoBar 12391 BstLean.Part154.csC ≤ 0.000258274119 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036256918320 : ℝ) / (1.295212 * 12391) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036256918321 : ℝ) / (1.29521 * 12391) := by gcongr
      _ ≤ (0.000258274119 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12391 BstLean.Part154.csC) ≤ 0.001033163182 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12391 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12391 BstLean.Part154.csC) (piBar (rhoBar 12391 BstLean.Part154.csC)) ≤ 0.000197271747 ∧
    cc1 (rhoBar 12391 BstLean.Part154.csC) (piBar (rhoBar 12391 BstLean.Part154.csC)) ≤ 0.000125525275 ∧
    cc2 (rhoBar 12391 BstLean.Part154.csC) ≤ 0.000072868326 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12391 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12391 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12391 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12391 BstLean.Part154.csC * nuR (rhoBar 12391 BstLean.Part154.csC)) ≤ 0.000516564915 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258274119 : ℝ) * 0.001033163182 := by gcongr
      _ ≤ (0.000516564915 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12391 BstLean.Part154.csC) * nuR (rhoBar 12391 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001033163182 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12391 BstLean.Part154.csC) * rhoBar 12391 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258274119 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258274119 / 2 + 0.399 * 0.001033163182 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197271747 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516564915 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125525275 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258274119 / 1.414213562 := by gcongr
      _ ≤ (0.000072868326 : ℝ) := by norm_num

end BstLean.Part269.N12391

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12391
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12391 BstLean.Part154.csC) (piBar (rhoBar 12391 BstLean.Part154.csC)) ≤ 1.68060E-7 := by
  have hr0 : 0 ≤ rhoBar 12391 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12391 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12391 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12391 BstLean.Part154.csC) (piBar (rhoBar 12391 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12391 BstLean.Part154.csC) (piBar (rhoBar 12391 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12391 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197271747 : ℝ) ^ 2 + 0.000125525275 ^ 2 + 3 * 0.000072868326 ^ 2 +
        2 * 0.797885 * 0.000197271747 * 0.000125525275 + 2 * 0.000197271747 * 0.000072868326 +
        4 * 0.797885 * 0.000125525275 * 0.000072868326 := by gcongr
    _ ≤ (1.68060E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12391 BstLean.Part154.csC Θ ≤ 0.002697190217 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12391 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12391 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12391 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12391 BstLean.Part154.csC) (piBar (rhoBar 12391 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12391 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036256918321 * 1.68060E-7 / (0.000258273720 : ℝ) := by gcongr
    _ ≤ 0.002697190217 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12391 BstLean.Part154.csC Θ ≤ 0.002993972576 + 0.000681535585 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12391 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12391 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12391 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036256918321 : ℝ) * ((2 * Θ * 0.000258274119 +
        (6863 / 10000) * 0.000258274119 * 12391 * 0.001033163182) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002993972576 + 0.000681535585 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12391 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12391 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12391 0.011 Θ ∧ gammaRatio 12391 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12391 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036256918321 : ℝ) * 0.525 / ((1 - 0.011) * 12391) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12391 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12391 0.011 Θ) :=
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
    badAllowance 12391 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12391 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12391 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12391 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12391 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12391 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12391 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12391 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12391 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12391 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12391 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036256918321 : ℝ) * 12391 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12391 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004093972576 + 0.003378725802 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12391

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12391
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12391 BstLean.Part154.csC) (piBar (rhoBar 12391 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12391 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12391 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12391 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12391 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12391 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12391 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12391 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12391 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12391 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12391 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12391 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12391 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12391 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12391 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053141835421 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12391) ≤ 0.010728464173 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12391 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036256918321)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010728464173 + 2 * 0.737676 / 12391) := by gcongr
    _ ≤ (0.053141835421 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12391 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12391

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12391
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489245920 : ℝ) ≤ plow 12391 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12391) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053374403623)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416024864) : eMP 12391 0.011 xi bn ≤ 0.001218688586 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12391 : ℝ) * (1 - 0.011))) ≤ 0.000602502809 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001416024864 / (12391 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602502809 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602502809 : ℝ) + 3.141593 * 0.053374403623 / (12391 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001218688586 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053374403623)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416024864) : PiBarMP 12391 12 0.011 xi bn ≤ 0.163271729561 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12391 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037630105820 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.700943988748 : ℝ) ≤ √((12391 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.314868728306 : ℝ) ≤ √(12391 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12391) ≤ 0.125162149693 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037630105820 + 0.053374403623 * 1.772454 / (2 * (110.700943988748 : ℝ))) * (1 + 0.001218688586) +
        8 / (12391 * 111.314868728306) + 0.125162149693 := by gcongr
    _ ≤ (0.163271729561 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053374403623)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416024864) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284170845771) :
    parallelOracle 12391 0.011 xi bn cd ≤ 0.164290711221 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12391 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12391 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489245920 : ℝ) ≤ plow 12391 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.314868728306 : ℝ) ≤ √(12391 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284170845771 : ℝ) / (2 * 0.560489245920 * 111.314868728306)) * 0.163271729561 +
        0.284170845771 ^ 2 / (2 * 0.560489245920 * 111.314868728306) := by gcongr
    _ ≤ (0.164290711221 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053374403623) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416024864)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284170845771) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12391 12391 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489245920 : ℝ) ≤ plow 12391 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.314868728306 : ℝ) ≤ √(12391 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12391 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12391 Θ 1.22 ≤ 0.011913058113 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.314868728306 := by gcongr <;> linarith
      _ ≤ (0.011913058113 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12391 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12391 12391 0.011 ≤ 0.008587236653 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12391 12391 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12391 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12391 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12391 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12391 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164290711221 + 0.011913058113 + (0.008587236653 : ℝ) *
        (1 + 2 * (0.284170845771 + 0.011913058113) / (0.560489245920 * 111.314868728306))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12391]

end BstLean.Part269.N12391

/-! The original eight local profiles supply actual 12391 moment certificates. -/
namespace BstLean.Part269.N12391
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12391 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12391 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12391 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053374403623 ∧
    0 ≤ bN 12391 BstLean.Part154.csC (groupTheta g) ∧ bN 12391 BstLean.Part154.csC (groupTheta g) ≤ 0.001416024864 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12391 12391 0.011
      (momentAllowance 12391 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12391 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12391 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12391 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12391 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12391 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231029010350 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12391 0.011
      (momentAllowance 12391 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12391 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12391
/-! The actual computed-centre upper energy formula at 12391. -/
namespace BstLean.Part269.N12391
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12391

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12391
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12391)
open BstLean.Part268 (cell12391)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086449123813
  | 2 => 0.087410869024
  | 3 => 0.088373741051
  | 4 => 0.089339828904
  | 5 => 0.090311634208
  | 6 => 0.091292129125
  | 7 => 0.092284819117
  | 8 => 0.093293810510
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12391 12391 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12391 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004098049004 + 0.003383255859 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S1.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12391

/-! Actual upper energy certificates on all 43 source endpoints at 12391. -/
namespace BstLean.Part269.N12391
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12391)
open BstLean.Part268 (cell12391)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12391 (gMinus 12391) (1 - (cell12391 i).lower) ≤ 1 ∧
    energyUpper 12391 (gMinus 12391) (BstLean.Part211.gPlus 12391)
      (finiteEnergy 12391 12391 0.011) (1 - (cell12391 i).lower) ≤
      (cell12391 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨10,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨11,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨12,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨13,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨14,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨15,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨16,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨17,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨18,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨19,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨20,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨21,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨22,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨23,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨24,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨25,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨26,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨27,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨28,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨29,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨30,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨31,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨32,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨33,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨34,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨35,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨36,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨37,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨38,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨39,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨40,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨41,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨42,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨43,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨44,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨45,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨46,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨47,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨48,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨49,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨50,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨51,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12391) (by norm_num)
        (q := 1 - (cell12391 ⟨52,by decide⟩).lower)
        (by norm_num [cell12391]) (by norm_num [cell12391])
      exact ⟨E.1,E.2.trans (by norm_num [cell12391])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12391

/-! Source-cell containment and simple scalar guards at 12391. -/
namespace BstLean.Part269.N12391
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12391)
open BstLean.Part268 (cell12391)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12391 ⟨10,by decide⟩).lower ∧ (cell12391 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12391 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12391 ⟨11,by decide⟩).lower ∧ (cell12391 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12391 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12391 ⟨12,by decide⟩).lower ∧ (cell12391 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12391 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12391 ⟨13,by decide⟩).lower ∧ (cell12391 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12391 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12391 ⟨14,by decide⟩).lower ∧ (cell12391 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12391 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12391 ⟨15,by decide⟩).lower ∧ (cell12391 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12391 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12391 ⟨16,by decide⟩).lower ∧ (cell12391 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12391 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12391 ⟨17,by decide⟩).lower ∧ (cell12391 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12391 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12391 ⟨18,by decide⟩).lower ∧ (cell12391 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12391 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12391 ⟨19,by decide⟩).lower ∧ (cell12391 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12391 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12391 ⟨20,by decide⟩).lower ∧ (cell12391 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12391 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12391 ⟨21,by decide⟩).lower ∧ (cell12391 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12391 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12391 ⟨22,by decide⟩).lower ∧ (cell12391 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12391 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12391 ⟨23,by decide⟩).lower ∧ (cell12391 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12391 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12391 ⟨24,by decide⟩).lower ∧ (cell12391 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12391 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12391 ⟨25,by decide⟩).lower ∧ (cell12391 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12391 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12391 ⟨26,by decide⟩).lower ∧ (cell12391 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12391 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12391 ⟨27,by decide⟩).lower ∧ (cell12391 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12391 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12391 ⟨28,by decide⟩).lower ∧ (cell12391 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12391 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12391 ⟨29,by decide⟩).lower ∧ (cell12391 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12391 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12391 ⟨30,by decide⟩).lower ∧ (cell12391 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12391 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12391 ⟨31,by decide⟩).lower ∧ (cell12391 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12391 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12391 ⟨32,by decide⟩).lower ∧ (cell12391 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12391 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12391 ⟨33,by decide⟩).lower ∧ (cell12391 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12391 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12391 ⟨34,by decide⟩).lower ∧ (cell12391 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12391 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12391 ⟨35,by decide⟩).lower ∧ (cell12391 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12391 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12391 ⟨36,by decide⟩).lower ∧ (cell12391 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12391 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12391 ⟨37,by decide⟩).lower ∧ (cell12391 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12391 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12391 ⟨38,by decide⟩).lower ∧ (cell12391 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12391 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12391 ⟨39,by decide⟩).lower ∧ (cell12391 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12391 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12391 ⟨40,by decide⟩).lower ∧ (cell12391 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12391 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12391 ⟨41,by decide⟩).lower ∧ (cell12391 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12391 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12391 ⟨42,by decide⟩).lower ∧ (cell12391 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12391 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12391 ⟨43,by decide⟩).lower ∧ (cell12391 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12391 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12391 ⟨44,by decide⟩).lower ∧ (cell12391 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12391 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12391 ⟨45,by decide⟩).lower ∧ (cell12391 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12391 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12391 ⟨46,by decide⟩).lower ∧ (cell12391 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12391 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12391 ⟨47,by decide⟩).lower ∧ (cell12391 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12391 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12391 ⟨48,by decide⟩).lower ∧ (cell12391 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12391 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12391 ⟨49,by decide⟩).lower ∧ (cell12391 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12391 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12391 ⟨50,by decide⟩).lower ∧ (cell12391 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12391 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12391 ⟨51,by decide⟩).lower ∧ (cell12391 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12391 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12391 ⟨52,by decide⟩).lower ∧ (cell12391 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12391 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12391 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12391 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12391,cell12391,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12391 i).lower ∧
    (cell12391 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12391 i).upper ≤ (0.532 : ℝ) ∧
    (cell12391 i).centre ≤ (0.1 : ℝ) ∧ (cell12391 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12391 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12391 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12391

/-! The local source numeric instances at 12391 have no network premises. -/
namespace BstLean.Part269.N12391
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12391)
open BstLean.Part268 (cell12391)

noncomputable def sourceNumerics12391 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12391 (cell12391 i)
      scalarRow12391.M scalarRow12391.H scalarRow12391.xi := by
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
    energy_allowance := scalarRow12391.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12391]
    centre_nonneg := (scalarRow12391.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12391])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12391
/-! Actual 12392 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12392
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12392 ≤ (1.036255442351 : ℝ) := by
  have hr : (111.319360400605 : ℝ) ≤ √(12392 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.319360400605 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12392 12392 (11 / 1000) ≤
    (0.008586890160 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12392) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.319360400605 : ℝ) ≤ √(12392 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12392)
  have hdiv : K / √(12392 : ℝ) ≤ K / 111.319360400605 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.319360400605 ≤ (0.008586890160 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12392.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12392 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12392 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12392 := gPlus_lower 12392
end BstLean.Part269.N12392

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12392
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036255442350 : ℝ) ≤ wn 12392 := by
  have hn : √(12392 : ℝ) ≤ 111.319360400606 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12392 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.319360400606 ≤ 2 / √(12392 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258252510 : ℝ) ≤ rhoBar 12392 BstLean.Part154.csC ∧
    rhoBar 12392 BstLean.Part154.csC ≤ 0.000258252910 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036255442350 : ℝ) / (1.295212 * 12392) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036255442351 : ℝ) / (1.29521 * 12392) := by gcongr
      _ ≤ (0.000258252910 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12392 BstLean.Part154.csC) ≤ 0.001033078335 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12392 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12392 BstLean.Part154.csC) (piBar (rhoBar 12392 BstLean.Part154.csC)) ≤ 0.000197255547 ∧
    cc1 (rhoBar 12392 BstLean.Part154.csC) (piBar (rhoBar 12392 BstLean.Part154.csC)) ≤ 0.000125514967 ∧
    cc2 (rhoBar 12392 BstLean.Part154.csC) ≤ 0.000072862342 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12392 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12392 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12392 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12392 BstLean.Part154.csC * nuR (rhoBar 12392 BstLean.Part154.csC)) ≤ 0.000516522494 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258252910 : ℝ) * 0.001033078335 := by gcongr
      _ ≤ (0.000516522494 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12392 BstLean.Part154.csC) * nuR (rhoBar 12392 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001033078335 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12392 BstLean.Part154.csC) * rhoBar 12392 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258252910 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258252910 / 2 + 0.399 * 0.001033078335 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197255547 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516522494 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125514967 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258252910 / 1.414213562 := by gcongr
      _ ≤ (0.000072862342 : ℝ) := by norm_num

end BstLean.Part269.N12392

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12392
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12392 BstLean.Part154.csC) (piBar (rhoBar 12392 BstLean.Part154.csC)) ≤ 1.68033E-7 := by
  have hr0 : 0 ≤ rhoBar 12392 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12392 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12392 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12392 BstLean.Part154.csC) (piBar (rhoBar 12392 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12392 BstLean.Part154.csC) (piBar (rhoBar 12392 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12392 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197255547 : ℝ) ^ 2 + 0.000125514967 ^ 2 + 3 * 0.000072862342 ^ 2 +
        2 * 0.797885 * 0.000197255547 * 0.000125514967 + 2 * 0.000197255547 * 0.000072862342 +
        4 * 0.797885 * 0.000125514967 * 0.000072862342 := by gcongr
    _ ≤ (1.68033E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12392 BstLean.Part154.csC Θ ≤ 0.002696974535 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12392 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12392 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12392 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12392 BstLean.Part154.csC) (piBar (rhoBar 12392 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12392 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036255442351 * 1.68033E-7 / (0.000258252510 : ℝ) := by gcongr
    _ ≤ 0.002696974535 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12392 BstLean.Part154.csC Θ ≤ 0.002993718182 + 0.000681478648 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12392 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12392 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12392 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036255442351 : ℝ) * ((2 * Θ * 0.000258252910 +
        (6863 / 10000) * 0.000258252910 * 12392 * 0.001033078335) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002993718182 + 0.000681478648 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12392 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12392 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12392 0.011 Θ ∧ gammaRatio 12392 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12392 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036255442351 : ℝ) * 0.525 / ((1 - 0.011) * 12392) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12392 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12392 0.011 Θ) :=
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
    badAllowance 12392 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12392 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12392 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12392 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12392 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12392 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12392 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12392 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12392 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12392 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12392 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036255442351 : ℝ) * 12392 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12392 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004093718182 + 0.003378453183 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12392

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12392
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12392 BstLean.Part154.csC) (piBar (rhoBar 12392 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12392 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12392 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12392 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12392 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12392 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12392 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12392 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12392 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12392 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12392 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12392 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12392 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12392 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12392 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053139667645 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12392) ≤ 0.010728031286 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12392 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036255442351)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010728031286 + 2 * 0.737676 / 12392) := by gcongr
    _ ≤ (0.053139667645 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12392 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12392

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12392
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489293423 : ℝ) ≤ plow 12392 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12392) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053374006104)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415911631) : eMP 12392 0.011 xi bn ≤ 0.001218590580 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12392 : ℝ) * (1 - 0.011))) ≤ 0.000602454409 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001415911631 / (12392 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602454409 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602454409 : ℝ) + 3.141593 * 0.053374006104 / (12392 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001218590580 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053374006104)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415911631) : PiBarMP 12392 12 0.011 xi bn ≤ 0.163265148043 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12392 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037628601237 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.705410888537 : ℝ) ≤ √((12392 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.319360400605 : ℝ) ≤ √(12392 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12392) ≤ 0.125157099472 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037628601237 + 0.053374006104 * 1.772454 / (2 * (110.705410888537 : ℝ))) * (1 + 0.001218590580) +
        8 / (12392 * 111.319360400605) + 0.125157099472 := by gcongr
    _ ≤ (0.163265148043 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053374006104)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415911631) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284167817671) :
    parallelOracle 12392 0.011 xi bn cd ≤ 0.164284055761 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12392 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12392 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489293423 : ℝ) ≤ plow 12392 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.319360400605 : ℝ) ≤ √(12392 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284167817671 : ℝ) / (2 * 0.560489293423 * 111.319360400605)) * 0.163265148043 +
        0.284167817671 ^ 2 / (2 * 0.560489293423 * 111.319360400605) := by gcongr
    _ ≤ (0.164284055761 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053374006104) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415911631)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284167817671) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12392 12392 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489293423 : ℝ) ≤ plow 12392 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.319360400605 : ℝ) ≤ √(12392 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12392 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12392 Θ 1.22 ≤ 0.011912577428 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.319360400605 := by gcongr <;> linarith
      _ ≤ (0.011912577428 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12392 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12392 12392 0.011 ≤ 0.008586890160 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12392 12392 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12392 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12392 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12392 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12392 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164284055761 + 0.011912577428 + (0.008586890160 : ℝ) *
        (1 + 2 * (0.284167817671 + 0.011912577428) / (0.560489293423 * 111.319360400605))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12392]

end BstLean.Part269.N12392

/-! The original eight local profiles supply actual 12392 moment certificates. -/
namespace BstLean.Part269.N12392
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12392 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12392 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12392 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053374006104 ∧
    0 ≤ bN 12392 BstLean.Part154.csC (groupTheta g) ∧ bN 12392 BstLean.Part154.csC (groupTheta g) ≤ 0.001415911631 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12392 12392 0.011
      (momentAllowance 12392 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12392 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12392 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12392 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12392 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12392 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231028150026 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12392 0.011
      (momentAllowance 12392 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12392 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12392
/-! The actual computed-centre upper energy formula at 12392. -/
namespace BstLean.Part269.N12392
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12392

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12392
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12392)
open BstLean.Part268 (cell12392)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086445813166
  | 2 => 0.087407487900
  | 3 => 0.088370277680
  | 4 => 0.089336268929
  | 5 => 0.090307960251
  | 6 => 0.091288320301
  | 7 => 0.092280850499
  | 8 => 0.093289652535
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12392 12392 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12392 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004098049004 + 0.003383255859 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S1.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12392

/-! Actual upper energy certificates on all 43 source endpoints at 12392. -/
namespace BstLean.Part269.N12392
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12392)
open BstLean.Part268 (cell12392)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12392 (gMinus 12392) (1 - (cell12392 i).lower) ≤ 1 ∧
    energyUpper 12392 (gMinus 12392) (BstLean.Part211.gPlus 12392)
      (finiteEnergy 12392 12392 0.011) (1 - (cell12392 i).lower) ≤
      (cell12392 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨10,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨11,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨12,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨13,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨14,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨15,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨16,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨17,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨18,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨19,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨20,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨21,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨22,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨23,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨24,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨25,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨26,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨27,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨28,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨29,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨30,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨31,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨32,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨33,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨34,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨35,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨36,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨37,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨38,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨39,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨40,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨41,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨42,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨43,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨44,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨45,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨46,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨47,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨48,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨49,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨50,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨51,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12392) (by norm_num)
        (q := 1 - (cell12392 ⟨52,by decide⟩).lower)
        (by norm_num [cell12392]) (by norm_num [cell12392])
      exact ⟨E.1,E.2.trans (by norm_num [cell12392])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12392

/-! Source-cell containment and simple scalar guards at 12392. -/
namespace BstLean.Part269.N12392
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12392)
open BstLean.Part268 (cell12392)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12392 ⟨10,by decide⟩).lower ∧ (cell12392 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12392 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12392 ⟨11,by decide⟩).lower ∧ (cell12392 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12392 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12392 ⟨12,by decide⟩).lower ∧ (cell12392 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12392 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12392 ⟨13,by decide⟩).lower ∧ (cell12392 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12392 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12392 ⟨14,by decide⟩).lower ∧ (cell12392 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12392 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12392 ⟨15,by decide⟩).lower ∧ (cell12392 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12392 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12392 ⟨16,by decide⟩).lower ∧ (cell12392 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12392 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12392 ⟨17,by decide⟩).lower ∧ (cell12392 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12392 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12392 ⟨18,by decide⟩).lower ∧ (cell12392 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12392 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12392 ⟨19,by decide⟩).lower ∧ (cell12392 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12392 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12392 ⟨20,by decide⟩).lower ∧ (cell12392 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12392 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12392 ⟨21,by decide⟩).lower ∧ (cell12392 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12392 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12392 ⟨22,by decide⟩).lower ∧ (cell12392 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12392 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12392 ⟨23,by decide⟩).lower ∧ (cell12392 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12392 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12392 ⟨24,by decide⟩).lower ∧ (cell12392 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12392 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12392 ⟨25,by decide⟩).lower ∧ (cell12392 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12392 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12392 ⟨26,by decide⟩).lower ∧ (cell12392 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12392 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12392 ⟨27,by decide⟩).lower ∧ (cell12392 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12392 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12392 ⟨28,by decide⟩).lower ∧ (cell12392 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12392 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12392 ⟨29,by decide⟩).lower ∧ (cell12392 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12392 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12392 ⟨30,by decide⟩).lower ∧ (cell12392 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12392 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12392 ⟨31,by decide⟩).lower ∧ (cell12392 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12392 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12392 ⟨32,by decide⟩).lower ∧ (cell12392 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12392 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12392 ⟨33,by decide⟩).lower ∧ (cell12392 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12392 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12392 ⟨34,by decide⟩).lower ∧ (cell12392 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12392 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12392 ⟨35,by decide⟩).lower ∧ (cell12392 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12392 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12392 ⟨36,by decide⟩).lower ∧ (cell12392 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12392 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12392 ⟨37,by decide⟩).lower ∧ (cell12392 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12392 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12392 ⟨38,by decide⟩).lower ∧ (cell12392 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12392 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12392 ⟨39,by decide⟩).lower ∧ (cell12392 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12392 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12392 ⟨40,by decide⟩).lower ∧ (cell12392 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12392 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12392 ⟨41,by decide⟩).lower ∧ (cell12392 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12392 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12392 ⟨42,by decide⟩).lower ∧ (cell12392 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12392 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12392 ⟨43,by decide⟩).lower ∧ (cell12392 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12392 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12392 ⟨44,by decide⟩).lower ∧ (cell12392 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12392 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12392 ⟨45,by decide⟩).lower ∧ (cell12392 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12392 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12392 ⟨46,by decide⟩).lower ∧ (cell12392 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12392 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12392 ⟨47,by decide⟩).lower ∧ (cell12392 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12392 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12392 ⟨48,by decide⟩).lower ∧ (cell12392 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12392 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12392 ⟨49,by decide⟩).lower ∧ (cell12392 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12392 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12392 ⟨50,by decide⟩).lower ∧ (cell12392 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12392 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12392 ⟨51,by decide⟩).lower ∧ (cell12392 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12392 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12392 ⟨52,by decide⟩).lower ∧ (cell12392 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12392 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12392 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12392 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12392,cell12392,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12392 i).lower ∧
    (cell12392 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12392 i).upper ≤ (0.532 : ℝ) ∧
    (cell12392 i).centre ≤ (0.1 : ℝ) ∧ (cell12392 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12392 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12392 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12392

/-! The local source numeric instances at 12392 have no network premises. -/
namespace BstLean.Part269.N12392
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12392)
open BstLean.Part268 (cell12392)

noncomputable def sourceNumerics12392 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12392 (cell12392 i)
      scalarRow12392.M scalarRow12392.H scalarRow12392.xi := by
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
    energy_allowance := scalarRow12392.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12392]
    centre_nonneg := (scalarRow12392.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12392])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12392
/-! Actual 12393 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12393
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12393 ≤ (1.036253966560 : ℝ) := by
  have hr : (111.323851891676 : ℝ) ≤ √(12393 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.323851891676 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12393 12393 (11 / 1000) ≤
    (0.008586543709 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12393) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.323851891676 : ℝ) ≤ √(12393 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12393)
  have hdiv : K / √(12393 : ℝ) ≤ K / 111.323851891676 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.323851891676 ≤ (0.008586543709 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12393.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12393 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12393 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12393 := gPlus_lower 12393
end BstLean.Part269.N12393

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12393
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036253966559 : ℝ) ≤ wn 12393 := by
  have hn : √(12393 : ℝ) ≤ 111.323851891677 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12393 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.323851891677 ≤ 2 / √(12393 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258231303 : ℝ) ≤ rhoBar 12393 BstLean.Part154.csC ∧
    rhoBar 12393 BstLean.Part154.csC ≤ 0.000258231703 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036253966559 : ℝ) / (1.295212 * 12393) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036253966560 : ℝ) / (1.29521 * 12393) := by gcongr
      _ ≤ (0.000258231703 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12393 BstLean.Part154.csC) ≤ 0.001032993496 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12393 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12393 BstLean.Part154.csC) (piBar (rhoBar 12393 BstLean.Part154.csC)) ≤ 0.000197239348 ∧
    cc1 (rhoBar 12393 BstLean.Part154.csC) (piBar (rhoBar 12393 BstLean.Part154.csC)) ≤ 0.000125504659 ∧
    cc2 (rhoBar 12393 BstLean.Part154.csC) ≤ 0.000072856358 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12393 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12393 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12393 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12393 BstLean.Part154.csC * nuR (rhoBar 12393 BstLean.Part154.csC)) ≤ 0.000516480077 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258231703 : ℝ) * 0.001032993496 := by gcongr
      _ ≤ (0.000516480077 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12393 BstLean.Part154.csC) * nuR (rhoBar 12393 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001032993496 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12393 BstLean.Part154.csC) * rhoBar 12393 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258231703 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258231703 / 2 + 0.399 * 0.001032993496 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197239348 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516480077 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125504659 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258231703 / 1.414213562 := by gcongr
      _ ≤ (0.000072856358 : ℝ) := by norm_num

end BstLean.Part269.N12393

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12393
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12393 BstLean.Part154.csC) (piBar (rhoBar 12393 BstLean.Part154.csC)) ≤ 1.68005E-7 := by
  have hr0 : 0 ≤ rhoBar 12393 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12393 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12393 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12393 BstLean.Part154.csC) (piBar (rhoBar 12393 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12393 BstLean.Part154.csC) (piBar (rhoBar 12393 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12393 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197239348 : ℝ) ^ 2 + 0.000125504659 ^ 2 + 3 * 0.000072856358 ^ 2 +
        2 * 0.797885 * 0.000197239348 * 0.000125504659 + 2 * 0.000197239348 * 0.000072856358 +
        4 * 0.797885 * 0.000125504659 * 0.000072856358 := by gcongr
    _ ≤ (1.68005E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12393 BstLean.Part154.csC Θ ≤ 0.002696742737 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12393 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12393 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12393 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12393 BstLean.Part154.csC) (piBar (rhoBar 12393 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12393 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036253966560 * 1.68005E-7 / (0.000258231303 : ℝ) := by gcongr
    _ ≤ 0.002696742737 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12393 BstLean.Part154.csC Θ ≤ 0.002993463796 + 0.000681421717 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12393 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12393 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12393 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036253966560 : ℝ) * ((2 * Θ * 0.000258231703 +
        (6863 / 10000) * 0.000258231703 * 12393 * 0.001032993496) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002993463796 + 0.000681421717 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12393 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12393 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12393 0.011 Θ ∧ gammaRatio 12393 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12393 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036253966560 : ℝ) * 0.525 / ((1 - 0.011) * 12393) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12393 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12393 0.011 Θ) :=
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
    badAllowance 12393 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12393 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12393 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12393 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12393 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12393 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12393 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12393 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12393 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12393 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12393 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036253966560 : ℝ) * 12393 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12393 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004093463796 + 0.003378164454 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12393

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12393
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12393 BstLean.Part154.csC) (piBar (rhoBar 12393 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12393 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12393 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12393 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12393 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12393 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12393 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12393 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12393 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12393 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12393 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12393 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12393 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12393 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12393 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053137500132 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12393) ≤ 0.010727598451 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12393 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036253966560)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010727598451 + 2 * 0.737676 / 12393) := by gcongr
    _ ≤ (0.053137500132 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12393 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12393

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12393
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489340918 : ℝ) ≤ plow 12393 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12393) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053373600135)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415789937) : eMP 12393 0.011 xi bn ≤ 0.001218488980 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12393 : ℝ) * (1 - 0.011))) ≤ 0.000602404213 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001415789937 / (12393 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602404213 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602404213 : ℝ) + 3.141593 * 0.053373600135 / (12393 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001218488980 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053373600135)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415789937) : PiBarMP 12393 12 0.011 xi bn ≤ 0.163258454305 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12393 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037626984161 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.709877608097 : ℝ) ≤ √((12393 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.323851891676 : ℝ) ≤ √(12393 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12393) ≤ 0.125152049862 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037626984161 + 0.053373600135 * 1.772454 / (2 * (110.709877608097 : ℝ))) * (1 + 0.001218488980) +
        8 / (12393 * 111.323851891676) + 0.125152049862 := by gcongr
    _ ≤ (0.163258454305 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053373600135)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415789937) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284164771542) :
    parallelOracle 12393 0.011 xi bn cd ≤ 0.164277287727 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12393 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12393 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489340918 : ℝ) ≤ plow 12393 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.323851891676 : ℝ) ≤ √(12393 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284164771542 : ℝ) / (2 * 0.560489340918 * 111.323851891676)) * 0.163258454305 +
        0.284164771542 ^ 2 / (2 * 0.560489340918 * 111.323851891676) := by gcongr
    _ ≤ (0.164277287727 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053373600135) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415789937)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284164771542) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12393 12393 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489340918 : ℝ) ≤ plow 12393 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.323851891676 : ℝ) ≤ √(12393 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12393 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12393 Θ 1.22 ≤ 0.011912096802 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.323851891676 := by gcongr <;> linarith
      _ ≤ (0.011912096802 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12393 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12393 12393 0.011 ≤ 0.008586543709 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12393 12393 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12393 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12393 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12393 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12393 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164277287727 + 0.011912096802 + (0.008586543709 : ℝ) *
        (1 + 2 * (0.284164771542 + 0.011912096802) / (0.560489340918 * 111.323851891676))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12393]

end BstLean.Part269.N12393

/-! The original eight local profiles supply actual 12393 moment certificates. -/
namespace BstLean.Part269.N12393
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12393 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12393 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12393 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053373600135 ∧
    0 ≤ bN 12393 BstLean.Part154.csC (groupTheta g) ∧ bN 12393 BstLean.Part154.csC (groupTheta g) ≤ 0.001415789937 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12393 12393 0.011
      (momentAllowance 12393 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12393 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12393 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12393 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12393 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12393 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231027271410 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12393 0.011
      (momentAllowance 12393 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12393 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12393
/-! The actual computed-centre upper energy formula at 12393. -/
namespace BstLean.Part269.N12393
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12393

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12393
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12393)
open BstLean.Part268 (cell12393)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086442504018
  | 2 => 0.087404108343
  | 3 => 0.088366815957
  | 4 => 0.089332710703
  | 5 => 0.090304288166
  | 6 => 0.091284513498
  | 7 => 0.092276884080
  | 8 => 0.093285496973
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12393 12393 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12393 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004098049004 + 0.003383255859 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S1.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12393

/-! Actual upper energy certificates on all 43 source endpoints at 12393. -/
namespace BstLean.Part269.N12393
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12393)
open BstLean.Part268 (cell12393)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12393 (gMinus 12393) (1 - (cell12393 i).lower) ≤ 1 ∧
    energyUpper 12393 (gMinus 12393) (BstLean.Part211.gPlus 12393)
      (finiteEnergy 12393 12393 0.011) (1 - (cell12393 i).lower) ≤
      (cell12393 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨10,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨11,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨12,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨13,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨14,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨15,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨16,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨17,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨18,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨19,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨20,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨21,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨22,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨23,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨24,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨25,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨26,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨27,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨28,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨29,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨30,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨31,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨32,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨33,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨34,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨35,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨36,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨37,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨38,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨39,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨40,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨41,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨42,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨43,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨44,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨45,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨46,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨47,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨48,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨49,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨50,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨51,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12393) (by norm_num)
        (q := 1 - (cell12393 ⟨52,by decide⟩).lower)
        (by norm_num [cell12393]) (by norm_num [cell12393])
      exact ⟨E.1,E.2.trans (by norm_num [cell12393])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12393

/-! Source-cell containment and simple scalar guards at 12393. -/
namespace BstLean.Part269.N12393
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12393)
open BstLean.Part268 (cell12393)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12393 ⟨10,by decide⟩).lower ∧ (cell12393 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12393 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12393 ⟨11,by decide⟩).lower ∧ (cell12393 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12393 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12393 ⟨12,by decide⟩).lower ∧ (cell12393 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12393 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12393 ⟨13,by decide⟩).lower ∧ (cell12393 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12393 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12393 ⟨14,by decide⟩).lower ∧ (cell12393 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12393 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12393 ⟨15,by decide⟩).lower ∧ (cell12393 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12393 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12393 ⟨16,by decide⟩).lower ∧ (cell12393 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12393 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12393 ⟨17,by decide⟩).lower ∧ (cell12393 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12393 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12393 ⟨18,by decide⟩).lower ∧ (cell12393 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12393 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12393 ⟨19,by decide⟩).lower ∧ (cell12393 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12393 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12393 ⟨20,by decide⟩).lower ∧ (cell12393 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12393 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12393 ⟨21,by decide⟩).lower ∧ (cell12393 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12393 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12393 ⟨22,by decide⟩).lower ∧ (cell12393 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12393 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12393 ⟨23,by decide⟩).lower ∧ (cell12393 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12393 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12393 ⟨24,by decide⟩).lower ∧ (cell12393 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12393 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12393 ⟨25,by decide⟩).lower ∧ (cell12393 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12393 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12393 ⟨26,by decide⟩).lower ∧ (cell12393 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12393 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12393 ⟨27,by decide⟩).lower ∧ (cell12393 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12393 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12393 ⟨28,by decide⟩).lower ∧ (cell12393 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12393 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12393 ⟨29,by decide⟩).lower ∧ (cell12393 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12393 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12393 ⟨30,by decide⟩).lower ∧ (cell12393 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12393 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12393 ⟨31,by decide⟩).lower ∧ (cell12393 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12393 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12393 ⟨32,by decide⟩).lower ∧ (cell12393 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12393 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12393 ⟨33,by decide⟩).lower ∧ (cell12393 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12393 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12393 ⟨34,by decide⟩).lower ∧ (cell12393 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12393 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12393 ⟨35,by decide⟩).lower ∧ (cell12393 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12393 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12393 ⟨36,by decide⟩).lower ∧ (cell12393 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12393 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12393 ⟨37,by decide⟩).lower ∧ (cell12393 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12393 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12393 ⟨38,by decide⟩).lower ∧ (cell12393 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12393 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12393 ⟨39,by decide⟩).lower ∧ (cell12393 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12393 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12393 ⟨40,by decide⟩).lower ∧ (cell12393 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12393 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12393 ⟨41,by decide⟩).lower ∧ (cell12393 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12393 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12393 ⟨42,by decide⟩).lower ∧ (cell12393 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12393 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12393 ⟨43,by decide⟩).lower ∧ (cell12393 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12393 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12393 ⟨44,by decide⟩).lower ∧ (cell12393 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12393 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12393 ⟨45,by decide⟩).lower ∧ (cell12393 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12393 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12393 ⟨46,by decide⟩).lower ∧ (cell12393 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12393 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12393 ⟨47,by decide⟩).lower ∧ (cell12393 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12393 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12393 ⟨48,by decide⟩).lower ∧ (cell12393 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12393 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12393 ⟨49,by decide⟩).lower ∧ (cell12393 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12393 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12393 ⟨50,by decide⟩).lower ∧ (cell12393 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12393 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12393 ⟨51,by decide⟩).lower ∧ (cell12393 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12393 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12393 ⟨52,by decide⟩).lower ∧ (cell12393 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12393 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12393 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12393 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12393,cell12393,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12393 i).lower ∧
    (cell12393 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12393 i).upper ≤ (0.532 : ℝ) ∧
    (cell12393 i).centre ≤ (0.1 : ℝ) ∧ (cell12393 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12393 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12393 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12393

/-! The local source numeric instances at 12393 have no network premises. -/
namespace BstLean.Part269.N12393
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12393)
open BstLean.Part268 (cell12393)

noncomputable def sourceNumerics12393 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12393 (cell12393 i)
      scalarRow12393.M scalarRow12393.H scalarRow12393.xi := by
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
    energy_allowance := scalarRow12393.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12393]
    centre_nonneg := (scalarRow12393.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12393])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12393
/-! Actual 12394 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12394
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12394 ≤ (1.036252490948 : ℝ) := by
  have hr : (111.328343201540 : ℝ) ≤ √(12394 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.328343201540 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12394 12394 (11 / 1000) ≤
    (0.008586197300 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12394) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.328343201540 : ℝ) ≤ √(12394 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12394)
  have hdiv : K / √(12394 : ℝ) ≤ K / 111.328343201540 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.328343201540 ≤ (0.008586197300 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12394.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12394 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12394 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12394 := gPlus_lower 12394
end BstLean.Part269.N12394

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12394
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036252490947 : ℝ) ≤ wn 12394 := by
  have hn : √(12394 : ℝ) ≤ 111.328343201541 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12394 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.328343201541 ≤ 2 / √(12394 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258210101 : ℝ) ≤ rhoBar 12394 BstLean.Part154.csC ∧
    rhoBar 12394 BstLean.Part154.csC ≤ 0.000258210500 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036252490947 : ℝ) / (1.295212 * 12394) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036252490948 : ℝ) / (1.29521 * 12394) := by gcongr
      _ ≤ (0.000258210500 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12394 BstLean.Part154.csC) ≤ 0.001032908673 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12394 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12394 BstLean.Part154.csC) (piBar (rhoBar 12394 BstLean.Part154.csC)) ≤ 0.000197223152 ∧
    cc1 (rhoBar 12394 BstLean.Part154.csC) (piBar (rhoBar 12394 BstLean.Part154.csC)) ≤ 0.000125494354 ∧
    cc2 (rhoBar 12394 BstLean.Part154.csC) ≤ 0.000072850376 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12394 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12394 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12394 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12394 BstLean.Part154.csC * nuR (rhoBar 12394 BstLean.Part154.csC)) ≤ 0.000516437668 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258210500 : ℝ) * 0.001032908673 := by gcongr
      _ ≤ (0.000516437668 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12394 BstLean.Part154.csC) * nuR (rhoBar 12394 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001032908673 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12394 BstLean.Part154.csC) * rhoBar 12394 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258210500 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258210500 / 2 + 0.399 * 0.001032908673 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197223152 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516437668 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125494354 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258210500 / 1.414213562 := by gcongr
      _ ≤ (0.000072850376 : ℝ) := by norm_num

end BstLean.Part269.N12394

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12394
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12394 BstLean.Part154.csC) (piBar (rhoBar 12394 BstLean.Part154.csC)) ≤ 1.67977E-7 := by
  have hr0 : 0 ≤ rhoBar 12394 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12394 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12394 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12394 BstLean.Part154.csC) (piBar (rhoBar 12394 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12394 BstLean.Part154.csC) (piBar (rhoBar 12394 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12394 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197223152 : ℝ) ^ 2 + 0.000125494354 ^ 2 + 3 * 0.000072850376 ^ 2 +
        2 * 0.797885 * 0.000197223152 * 0.000125494354 + 2 * 0.000197223152 * 0.000072850376 +
        4 * 0.797885 * 0.000125494354 * 0.000072850376 := by gcongr
    _ ≤ (1.67977E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12394 BstLean.Part154.csC Θ ≤ 0.002696510850 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12394 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12394 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12394 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12394 BstLean.Part154.csC) (piBar (rhoBar 12394 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12394 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036252490948 * 1.67977E-7 / (0.000258210101 : ℝ) := by gcongr
    _ ≤ 0.002696510850 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12394 BstLean.Part154.csC Θ ≤ 0.002993209466 + 0.000681364796 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12394 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12394 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12394 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036252490948 : ℝ) * ((2 * Θ * 0.000258210500 +
        (6863 / 10000) * 0.000258210500 * 12394 * 0.001032908673) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002993209466 + 0.000681364796 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12394 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12394 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12394 0.011 Θ ∧ gammaRatio 12394 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12394 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036252490948 : ℝ) * 0.525 / ((1 - 0.011) * 12394) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12394 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12394 0.011 Θ) :=
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
    badAllowance 12394 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12394 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12394 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12394 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12394 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12394 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12394 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12394 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12394 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12394 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12394 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036252490948 : ℝ) * 12394 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12394 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004093209466 + 0.003377875646 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12394

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12394
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12394 BstLean.Part154.csC) (piBar (rhoBar 12394 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12394 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12394 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12394 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12394 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12394 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12394 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12394 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12394 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12394 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12394 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12394 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12394 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12394 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12394 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053135332881 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12394) ≤ 0.010727165668 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12394 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036252490948)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010727165668 + 2 * 0.737676 / 12394) := by gcongr
    _ ≤ (0.053135332881 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12394 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12394

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12394
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489388405 : ℝ) ≤ plow 12394 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12394) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053373194181)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415668197) : eMP 12394 0.011 xi bn ≤ 0.001218387368 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12394 : ℝ) * (1 - 0.011))) ≤ 0.000602354011 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001415668197 / (12394 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602354011 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602354011 : ℝ) + 3.141593 * 0.053373194181 / (12394 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001218387368 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053373194181)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415668197) : PiBarMP 12394 12 0.011 xi bn ≤ 0.163251760499 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12394 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037625366404 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.714344147450 : ℝ) ≤ √((12394 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.328343201540 : ℝ) ≤ √(12394 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12394) ≤ 0.125147000864 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037625366404 + 0.053373194181 * 1.772454 / (2 * (110.714344147450 : ℝ))) * (1 + 0.001218387368) +
        8 / (12394 * 111.328343201540) + 0.125147000864 := by gcongr
    _ ≤ (0.163251760499 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053373194181)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415668197) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284161725705) :
    parallelOracle 12394 0.011 xi bn cd ≤ 0.164270519635 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12394 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12394 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489388405 : ℝ) ≤ plow 12394 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.328343201540 : ℝ) ≤ √(12394 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284161725705 : ℝ) / (2 * 0.560489388405 * 111.328343201540)) * 0.163251760499 +
        0.284161725705 ^ 2 / (2 * 0.560489388405 * 111.328343201540) := by gcongr
    _ ≤ (0.164270519635 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053373194181) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415668197)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284161725705) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12394 12394 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489388405 : ℝ) ≤ plow 12394 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.328343201540 : ℝ) ≤ √(12394 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12394 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12394 Θ 1.22 ≤ 0.011911616233 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.328343201540 := by gcongr <;> linarith
      _ ≤ (0.011911616233 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12394 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12394 12394 0.011 ≤ 0.008586197300 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12394 12394 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12394 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12394 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12394 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12394 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164270519635 + 0.011911616233 + (0.008586197300 : ℝ) *
        (1 + 2 * (0.284161725705 + 0.011911616233) / (0.560489388405 * 111.328343201540))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12394]

end BstLean.Part269.N12394

/-! The original eight local profiles supply actual 12394 moment certificates. -/
namespace BstLean.Part269.N12394
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12394 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12394 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12394 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053373194181 ∧
    0 ≤ bN 12394 BstLean.Part154.csC (groupTheta g) ∧ bN 12394 BstLean.Part154.csC (groupTheta g) ≤ 0.001415668197 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12394 12394 0.011
      (momentAllowance 12394 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12394 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12394 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12394 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12394 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12394 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231026392824 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12394 0.011
      (momentAllowance 12394 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12394 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12394
/-! The actual computed-centre upper energy formula at 12394. -/
namespace BstLean.Part269.N12394
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12394

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12394
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12394)
open BstLean.Part268 (cell12394)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086439196369
  | 2 => 0.087400730349
  | 3 => 0.088363355881
  | 4 => 0.089329154224
  | 5 => 0.090300617950
  | 6 => 0.091280708711
  | 7 => 0.092272919856
  | 8 => 0.093281343821
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12394 12394 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12394 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004098049004 + 0.003383255859 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S1.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12394

/-! Actual upper energy certificates on all 43 source endpoints at 12394. -/
namespace BstLean.Part269.N12394
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12394)
open BstLean.Part268 (cell12394)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12394 (gMinus 12394) (1 - (cell12394 i).lower) ≤ 1 ∧
    energyUpper 12394 (gMinus 12394) (BstLean.Part211.gPlus 12394)
      (finiteEnergy 12394 12394 0.011) (1 - (cell12394 i).lower) ≤
      (cell12394 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨10,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨11,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨12,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨13,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨14,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨15,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨16,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨17,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨18,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨19,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨20,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨21,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨22,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨23,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨24,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨25,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨26,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨27,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨28,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨29,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨30,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨31,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨32,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨33,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨34,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨35,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨36,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨37,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨38,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨39,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨40,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨41,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨42,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨43,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨44,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨45,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨46,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨47,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨48,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨49,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨50,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨51,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12394) (by norm_num)
        (q := 1 - (cell12394 ⟨52,by decide⟩).lower)
        (by norm_num [cell12394]) (by norm_num [cell12394])
      exact ⟨E.1,E.2.trans (by norm_num [cell12394])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12394

/-! Source-cell containment and simple scalar guards at 12394. -/
namespace BstLean.Part269.N12394
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12394)
open BstLean.Part268 (cell12394)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12394 ⟨10,by decide⟩).lower ∧ (cell12394 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12394 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12394 ⟨11,by decide⟩).lower ∧ (cell12394 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12394 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12394 ⟨12,by decide⟩).lower ∧ (cell12394 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12394 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12394 ⟨13,by decide⟩).lower ∧ (cell12394 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12394 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12394 ⟨14,by decide⟩).lower ∧ (cell12394 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12394 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12394 ⟨15,by decide⟩).lower ∧ (cell12394 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12394 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12394 ⟨16,by decide⟩).lower ∧ (cell12394 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12394 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12394 ⟨17,by decide⟩).lower ∧ (cell12394 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12394 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12394 ⟨18,by decide⟩).lower ∧ (cell12394 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12394 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12394 ⟨19,by decide⟩).lower ∧ (cell12394 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12394 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12394 ⟨20,by decide⟩).lower ∧ (cell12394 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12394 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12394 ⟨21,by decide⟩).lower ∧ (cell12394 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12394 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12394 ⟨22,by decide⟩).lower ∧ (cell12394 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12394 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12394 ⟨23,by decide⟩).lower ∧ (cell12394 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12394 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12394 ⟨24,by decide⟩).lower ∧ (cell12394 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12394 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12394 ⟨25,by decide⟩).lower ∧ (cell12394 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12394 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12394 ⟨26,by decide⟩).lower ∧ (cell12394 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12394 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12394 ⟨27,by decide⟩).lower ∧ (cell12394 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12394 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12394 ⟨28,by decide⟩).lower ∧ (cell12394 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12394 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12394 ⟨29,by decide⟩).lower ∧ (cell12394 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12394 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12394 ⟨30,by decide⟩).lower ∧ (cell12394 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12394 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12394 ⟨31,by decide⟩).lower ∧ (cell12394 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12394 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12394 ⟨32,by decide⟩).lower ∧ (cell12394 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12394 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12394 ⟨33,by decide⟩).lower ∧ (cell12394 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12394 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12394 ⟨34,by decide⟩).lower ∧ (cell12394 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12394 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12394 ⟨35,by decide⟩).lower ∧ (cell12394 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12394 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12394 ⟨36,by decide⟩).lower ∧ (cell12394 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12394 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12394 ⟨37,by decide⟩).lower ∧ (cell12394 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12394 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12394 ⟨38,by decide⟩).lower ∧ (cell12394 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12394 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12394 ⟨39,by decide⟩).lower ∧ (cell12394 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12394 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12394 ⟨40,by decide⟩).lower ∧ (cell12394 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12394 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12394 ⟨41,by decide⟩).lower ∧ (cell12394 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12394 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12394 ⟨42,by decide⟩).lower ∧ (cell12394 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12394 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12394 ⟨43,by decide⟩).lower ∧ (cell12394 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12394 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12394 ⟨44,by decide⟩).lower ∧ (cell12394 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12394 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12394 ⟨45,by decide⟩).lower ∧ (cell12394 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12394 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12394 ⟨46,by decide⟩).lower ∧ (cell12394 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12394 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12394 ⟨47,by decide⟩).lower ∧ (cell12394 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12394 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12394 ⟨48,by decide⟩).lower ∧ (cell12394 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12394 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12394 ⟨49,by decide⟩).lower ∧ (cell12394 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12394 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12394 ⟨50,by decide⟩).lower ∧ (cell12394 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12394 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12394 ⟨51,by decide⟩).lower ∧ (cell12394 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12394 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12394 ⟨52,by decide⟩).lower ∧ (cell12394 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12394 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12394 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12394 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12394,cell12394,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12394 i).lower ∧
    (cell12394 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12394 i).upper ≤ (0.532 : ℝ) ∧
    (cell12394 i).centre ≤ (0.1 : ℝ) ∧ (cell12394 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12394 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12394 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12394

/-! The local source numeric instances at 12394 have no network premises. -/
namespace BstLean.Part269.N12394
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12394)
open BstLean.Part268 (cell12394)

noncomputable def sourceNumerics12394 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12394 (cell12394 i)
      scalarRow12394.M scalarRow12394.H scalarRow12394.xi := by
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
    energy_allowance := scalarRow12394.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12394]
    centre_nonneg := (scalarRow12394.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12394])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12394
/-! Actual 12395 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12395
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12395 ≤ (1.036251015517 : ℝ) := by
  have hr : (111.332834330219 : ℝ) ≤ √(12395 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.332834330219 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12395 12395 (11 / 1000) ≤
    (0.008585850933 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12395) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.332834330219 : ℝ) ≤ √(12395 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12395)
  have hdiv : K / √(12395 : ℝ) ≤ K / 111.332834330219 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.332834330219 ≤ (0.008585850933 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12395.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12395 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12395 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12395 := gPlus_lower 12395
end BstLean.Part269.N12395

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12395
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036251015516 : ℝ) ≤ wn 12395 := by
  have hn : √(12395 : ℝ) ≤ 111.332834330220 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12395 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.332834330220 ≤ 2 / √(12395 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258188901 : ℝ) ≤ rhoBar 12395 BstLean.Part154.csC ∧
    rhoBar 12395 BstLean.Part154.csC ≤ 0.000258189301 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036251015516 : ℝ) / (1.295212 * 12395) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036251015517 : ℝ) / (1.29521 * 12395) := by gcongr
      _ ≤ (0.000258189301 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12395 BstLean.Part154.csC) ≤ 0.001032823866 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12395 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12395 BstLean.Part154.csC) (piBar (rhoBar 12395 BstLean.Part154.csC)) ≤ 0.000197206960 ∧
    cc1 (rhoBar 12395 BstLean.Part154.csC) (piBar (rhoBar 12395 BstLean.Part154.csC)) ≤ 0.000125484051 ∧
    cc2 (rhoBar 12395 BstLean.Part154.csC) ≤ 0.000072844395 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12395 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12395 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12395 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12395 BstLean.Part154.csC * nuR (rhoBar 12395 BstLean.Part154.csC)) ≤ 0.000516395268 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258189301 : ℝ) * 0.001032823866 := by gcongr
      _ ≤ (0.000516395268 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12395 BstLean.Part154.csC) * nuR (rhoBar 12395 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001032823866 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12395 BstLean.Part154.csC) * rhoBar 12395 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258189301 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258189301 / 2 + 0.399 * 0.001032823866 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197206960 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516395268 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125484051 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258189301 / 1.414213562 := by gcongr
      _ ≤ (0.000072844395 : ℝ) := by norm_num

end BstLean.Part269.N12395

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12395
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12395 BstLean.Part154.csC) (piBar (rhoBar 12395 BstLean.Part154.csC)) ≤ 1.67950E-7 := by
  have hr0 : 0 ≤ rhoBar 12395 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12395 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12395 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12395 BstLean.Part154.csC) (piBar (rhoBar 12395 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12395 BstLean.Part154.csC) (piBar (rhoBar 12395 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12395 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197206960 : ℝ) ^ 2 + 0.000125484051 ^ 2 + 3 * 0.000072844395 ^ 2 +
        2 * 0.797885 * 0.000197206960 * 0.000125484051 + 2 * 0.000197206960 * 0.000072844395 +
        4 * 0.797885 * 0.000125484051 * 0.000072844395 := by gcongr
    _ ≤ (1.67950E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12395 BstLean.Part154.csC Θ ≤ 0.002696294959 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12395 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12395 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12395 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12395 BstLean.Part154.csC) (piBar (rhoBar 12395 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12395 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036251015517 * 1.67950E-7 / (0.000258188901 : ℝ) := by gcongr
    _ ≤ 0.002696294959 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12395 BstLean.Part154.csC Θ ≤ 0.002992955191 + 0.000681307886 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12395 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12395 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12395 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036251015517 : ℝ) * ((2 * Θ * 0.000258189301 +
        (6863 / 10000) * 0.000258189301 * 12395 * 0.001032823866) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002992955191 + 0.000681307886 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12395 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12395 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12395 0.011 Θ ∧ gammaRatio 12395 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12395 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036251015517 : ℝ) * 0.525 / ((1 - 0.011) * 12395) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12395 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12395 0.011 Θ) :=
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
    badAllowance 12395 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12395 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12395 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12395 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12395 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12395 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12395 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12395 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12395 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12395 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12395 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036251015517 : ℝ) * 12395 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12395 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004092955191 + 0.003377602845 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12395

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12395
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12395 BstLean.Part154.csC) (piBar (rhoBar 12395 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12395 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12395 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12395 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12395 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12395 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12395 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12395 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12395 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12395 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12395 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12395 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12395 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12395 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12395 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053133165897 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12395) ≤ 0.010726732938 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12395 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036251015517)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010726732938 + 2 * 0.737676 / 12395) := by gcongr
    _ ≤ (0.053133165897 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12395 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12395

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12395
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489435885 : ℝ) ≤ plow 12395 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12395) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053372796685)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415554854) : eMP 12395 0.011 xi bn ≤ 0.001218289341 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12395 : ℝ) * (1 - 0.011))) ≤ 0.000602305600 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001415554854 / (12395 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602305600 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602305600 : ℝ) + 3.141593 * 0.053372796685 / (12395 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001218289341 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053372796685)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415554854) : PiBarMP 12395 12 0.011 xi bn ≤ 0.163245179168 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12395 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037623860169 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.718810506616 : ℝ) ≤ √((12395 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.332834330219 : ℝ) ≤ √(12395 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12395) ≤ 0.125141952476 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037623860169 + 0.053372796685 * 1.772454 / (2 * (110.718810506616 : ℝ))) * (1 + 0.001218289341) +
        8 / (12395 * 111.332834330219) + 0.125141952476 := by gcongr
    _ ≤ (0.163245179168 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053372796685)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415554854) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284158698437) :
    parallelOracle 12395 0.011 xi bn cd ≤ 0.164263864391 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12395 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12395 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489435885 : ℝ) ≤ plow 12395 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.332834330219 : ℝ) ≤ √(12395 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284158698437 : ℝ) / (2 * 0.560489435885 * 111.332834330219)) * 0.163245179168 +
        0.284158698437 ^ 2 / (2 * 0.560489435885 * 111.332834330219) := by gcongr
    _ ≤ (0.164263864391 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053372796685) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415554854)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284158698437) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12395 12395 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489435885 : ℝ) ≤ plow 12395 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.332834330219 : ℝ) ≤ √(12395 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12395 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12395 Θ 1.22 ≤ 0.011911135722 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.332834330219 := by gcongr <;> linarith
      _ ≤ (0.011911135722 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12395 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12395 12395 0.011 ≤ 0.008585850933 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12395 12395 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12395 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12395 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12395 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12395 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164263864391 + 0.011911135722 + (0.008585850933 : ℝ) *
        (1 + 2 * (0.284158698437 + 0.011911135722) / (0.560489435885 * 111.332834330219))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12395]

end BstLean.Part269.N12395

/-! The original eight local profiles supply actual 12395 moment certificates. -/
namespace BstLean.Part269.N12395
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12395 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12395 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12395 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053372796685 ∧
    0 ≤ bN 12395 BstLean.Part154.csC (groupTheta g) ∧ bN 12395 BstLean.Part154.csC (groupTheta g) ≤ 0.001415554854 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12395 12395 0.011
      (momentAllowance 12395 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12395 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12395 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12395 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12395 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12395 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231025532540 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12395 0.011
      (momentAllowance 12395 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12395 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12395
/-! The actual computed-centre upper energy formula at 12395. -/
namespace BstLean.Part269.N12395
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12395

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12395
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12395)
open BstLean.Part268 (cell12395)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086435890215
  | 2 => 0.087397353919
  | 3 => 0.088359897449
  | 4 => 0.089325599490
  | 5 => 0.090296949601
  | 6 => 0.091276905940
  | 7 => 0.092268957825
  | 8 => 0.093277193075
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12395 12395 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12395 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004098049004 + 0.003383255859 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S1.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12395

/-! Actual upper energy certificates on all 43 source endpoints at 12395. -/
namespace BstLean.Part269.N12395
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12395)
open BstLean.Part268 (cell12395)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12395 (gMinus 12395) (1 - (cell12395 i).lower) ≤ 1 ∧
    energyUpper 12395 (gMinus 12395) (BstLean.Part211.gPlus 12395)
      (finiteEnergy 12395 12395 0.011) (1 - (cell12395 i).lower) ≤
      (cell12395 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨10,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨11,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨12,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨13,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨14,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨15,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨16,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨17,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨18,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨19,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨20,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨21,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨22,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨23,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨24,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨25,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨26,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨27,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨28,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨29,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨30,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨31,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨32,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨33,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨34,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨35,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨36,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨37,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨38,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨39,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨40,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨41,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨42,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨43,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨44,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨45,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨46,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨47,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨48,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨49,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨50,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨51,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12395) (by norm_num)
        (q := 1 - (cell12395 ⟨52,by decide⟩).lower)
        (by norm_num [cell12395]) (by norm_num [cell12395])
      exact ⟨E.1,E.2.trans (by norm_num [cell12395])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12395

/-! Source-cell containment and simple scalar guards at 12395. -/
namespace BstLean.Part269.N12395
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12395)
open BstLean.Part268 (cell12395)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12395 ⟨10,by decide⟩).lower ∧ (cell12395 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12395 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12395 ⟨11,by decide⟩).lower ∧ (cell12395 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12395 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12395 ⟨12,by decide⟩).lower ∧ (cell12395 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12395 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12395 ⟨13,by decide⟩).lower ∧ (cell12395 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12395 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12395 ⟨14,by decide⟩).lower ∧ (cell12395 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12395 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12395 ⟨15,by decide⟩).lower ∧ (cell12395 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12395 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12395 ⟨16,by decide⟩).lower ∧ (cell12395 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12395 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12395 ⟨17,by decide⟩).lower ∧ (cell12395 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12395 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12395 ⟨18,by decide⟩).lower ∧ (cell12395 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12395 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12395 ⟨19,by decide⟩).lower ∧ (cell12395 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12395 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12395 ⟨20,by decide⟩).lower ∧ (cell12395 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12395 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12395 ⟨21,by decide⟩).lower ∧ (cell12395 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12395 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12395 ⟨22,by decide⟩).lower ∧ (cell12395 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12395 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12395 ⟨23,by decide⟩).lower ∧ (cell12395 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12395 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12395 ⟨24,by decide⟩).lower ∧ (cell12395 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12395 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12395 ⟨25,by decide⟩).lower ∧ (cell12395 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12395 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12395 ⟨26,by decide⟩).lower ∧ (cell12395 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12395 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12395 ⟨27,by decide⟩).lower ∧ (cell12395 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12395 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12395 ⟨28,by decide⟩).lower ∧ (cell12395 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12395 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12395 ⟨29,by decide⟩).lower ∧ (cell12395 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12395 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12395 ⟨30,by decide⟩).lower ∧ (cell12395 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12395 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12395 ⟨31,by decide⟩).lower ∧ (cell12395 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12395 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12395 ⟨32,by decide⟩).lower ∧ (cell12395 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12395 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12395 ⟨33,by decide⟩).lower ∧ (cell12395 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12395 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12395 ⟨34,by decide⟩).lower ∧ (cell12395 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12395 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12395 ⟨35,by decide⟩).lower ∧ (cell12395 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12395 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12395 ⟨36,by decide⟩).lower ∧ (cell12395 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12395 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12395 ⟨37,by decide⟩).lower ∧ (cell12395 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12395 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12395 ⟨38,by decide⟩).lower ∧ (cell12395 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12395 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12395 ⟨39,by decide⟩).lower ∧ (cell12395 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12395 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12395 ⟨40,by decide⟩).lower ∧ (cell12395 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12395 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12395 ⟨41,by decide⟩).lower ∧ (cell12395 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12395 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12395 ⟨42,by decide⟩).lower ∧ (cell12395 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12395 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12395 ⟨43,by decide⟩).lower ∧ (cell12395 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12395 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12395 ⟨44,by decide⟩).lower ∧ (cell12395 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12395 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12395 ⟨45,by decide⟩).lower ∧ (cell12395 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12395 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12395 ⟨46,by decide⟩).lower ∧ (cell12395 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12395 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12395 ⟨47,by decide⟩).lower ∧ (cell12395 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12395 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12395 ⟨48,by decide⟩).lower ∧ (cell12395 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12395 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12395 ⟨49,by decide⟩).lower ∧ (cell12395 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12395 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12395 ⟨50,by decide⟩).lower ∧ (cell12395 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12395 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12395 ⟨51,by decide⟩).lower ∧ (cell12395 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12395 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12395 ⟨52,by decide⟩).lower ∧ (cell12395 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12395 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12395 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12395 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12395,cell12395,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12395 i).lower ∧
    (cell12395 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12395 i).upper ≤ (0.532 : ℝ) ∧
    (cell12395 i).centre ≤ (0.1 : ℝ) ∧ (cell12395 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12395 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12395 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12395

/-! The local source numeric instances at 12395 have no network premises. -/
namespace BstLean.Part269.N12395
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12395)
open BstLean.Part268 (cell12395)

noncomputable def sourceNumerics12395 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12395 (cell12395 i)
      scalarRow12395.M scalarRow12395.H scalarRow12395.xi := by
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
    energy_allowance := scalarRow12395.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12395]
    centre_nonneg := (scalarRow12395.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12395])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12395
/-! Actual 12396 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12396
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12396 ≤ (1.036249540264 : ℝ) := by
  have hr : (111.337325277734 : ℝ) ≤ √(12396 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.337325277734 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12396 12396 (11 / 1000) ≤
    (0.008585504608 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12396) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.337325277734 : ℝ) ≤ √(12396 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12396)
  have hdiv : K / √(12396 : ℝ) ≤ K / 111.337325277734 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.337325277734 ≤ (0.008585504608 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12396.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12396 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12396 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12396 := gPlus_lower 12396
end BstLean.Part269.N12396

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12396
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036249540263 : ℝ) ≤ wn 12396 := by
  have hn : √(12396 : ℝ) ≤ 111.337325277735 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12396 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.337325277735 ≤ 2 / √(12396 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258167705 : ℝ) ≤ rhoBar 12396 BstLean.Part154.csC ∧
    rhoBar 12396 BstLean.Part154.csC ≤ 0.000258168105 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036249540263 : ℝ) / (1.295212 * 12396) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036249540264 : ℝ) / (1.29521 * 12396) := by gcongr
      _ ≤ (0.000258168105 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12396 BstLean.Part154.csC) ≤ 0.001032739071 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12396 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12396 BstLean.Part154.csC) (piBar (rhoBar 12396 BstLean.Part154.csC)) ≤ 0.000197190769 ∧
    cc1 (rhoBar 12396 BstLean.Part154.csC) (piBar (rhoBar 12396 BstLean.Part154.csC)) ≤ 0.000125473749 ∧
    cc2 (rhoBar 12396 BstLean.Part154.csC) ≤ 0.000072838415 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12396 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12396 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12396 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12396 BstLean.Part154.csC * nuR (rhoBar 12396 BstLean.Part154.csC)) ≤ 0.000516352873 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258168105 : ℝ) * 0.001032739071 := by gcongr
      _ ≤ (0.000516352873 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12396 BstLean.Part154.csC) * nuR (rhoBar 12396 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001032739071 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12396 BstLean.Part154.csC) * rhoBar 12396 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258168105 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258168105 / 2 + 0.399 * 0.001032739071 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197190769 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516352873 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125473749 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258168105 / 1.414213562 := by gcongr
      _ ≤ (0.000072838415 : ℝ) := by norm_num

end BstLean.Part269.N12396

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12396
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12396 BstLean.Part154.csC) (piBar (rhoBar 12396 BstLean.Part154.csC)) ≤ 1.67922E-7 := by
  have hr0 : 0 ≤ rhoBar 12396 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12396 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12396 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12396 BstLean.Part154.csC) (piBar (rhoBar 12396 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12396 BstLean.Part154.csC) (piBar (rhoBar 12396 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12396 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197190769 : ℝ) ^ 2 + 0.000125473749 ^ 2 + 3 * 0.000072838415 ^ 2 +
        2 * 0.797885 * 0.000197190769 * 0.000125473749 + 2 * 0.000197190769 * 0.000072838415 +
        4 * 0.797885 * 0.000125473749 * 0.000072838415 := by gcongr
    _ ≤ (1.67922E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12396 BstLean.Part154.csC Θ ≤ 0.002696062938 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12396 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12396 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12396 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12396 BstLean.Part154.csC) (piBar (rhoBar 12396 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12396 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036249540264 * 1.67922E-7 / (0.000258167705 : ℝ) := by gcongr
    _ ≤ 0.002696062938 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12396 BstLean.Part154.csC Θ ≤ 0.002992700947 + 0.000681250984 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12396 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12396 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12396 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036249540264 : ℝ) * ((2 * Θ * 0.000258168105 +
        (6863 / 10000) * 0.000258168105 * 12396 * 0.001032739071) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002992700947 + 0.000681250984 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12396 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12396 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12396 0.011 Θ ∧ gammaRatio 12396 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12396 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036249540264 : ℝ) * 0.525 / ((1 - 0.011) * 12396) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12396 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12396 0.011 Θ) :=
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
    badAllowance 12396 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12396 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12396 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12396 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12396 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12396 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12396 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12396 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12396 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12396 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12396 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036249540264 : ℝ) * 12396 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12396 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004092700947 + 0.003377313922 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12396

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12396
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12396 BstLean.Part154.csC) (piBar (rhoBar 12396 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12396 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12396 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12396 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12396 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12396 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12396 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12396 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12396 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12396 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12396 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12396 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12396 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12396 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12396 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053130999175 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12396) ≤ 0.010726300260 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12396 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036249540264)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010726300260 + 2 * 0.737676 / 12396) := by gcongr
    _ ≤ (0.053130999175 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12396 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12396

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12396
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489483357 : ℝ) ≤ plow 12396 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12396) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053372390757)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415433043) : eMP 12396 0.011 xi bn ≤ 0.001218187715 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12396 : ℝ) * (1 - 0.011))) ≤ 0.000602255391 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001415433043 / (12396 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602255391 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602255391 : ℝ) + 3.141593 * 0.053372390757 / (12396 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001218187715 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053372390757)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415433043) : PiBarMP 12396 12 0.011 xi bn ≤ 0.163238485511 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12396 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037622241335 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.723276685618 : ℝ) ≤ √((12396 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.337325277734 : ℝ) ≤ √(12396 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12396) ≤ 0.125136904700 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037622241335 + 0.053372390757 * 1.772454 / (2 * (110.723276685618 : ℝ))) * (1 + 0.001218187715) +
        8 / (12396 * 111.337325277734) + 0.125136904700 := by gcongr
    _ ≤ (0.163238485511 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053372390757)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415433043) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284155653178) :
    parallelOracle 12396 0.011 xi bn cd ≤ 0.164257096468 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12396 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12396 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489483357 : ℝ) ≤ plow 12396 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.337325277734 : ℝ) ≤ √(12396 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284155653178 : ℝ) / (2 * 0.560489483357 * 111.337325277734)) * 0.163238485511 +
        0.284155653178 ^ 2 / (2 * 0.560489483357 * 111.337325277734) := by gcongr
    _ ≤ (0.164257096468 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053372390757) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415433043)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284155653178) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12396 12396 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489483357 : ℝ) ≤ plow 12396 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.337325277734 : ℝ) ≤ √(12396 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12396 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12396 Θ 1.22 ≤ 0.011910655270 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.337325277734 := by gcongr <;> linarith
      _ ≤ (0.011910655270 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12396 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12396 12396 0.011 ≤ 0.008585504608 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12396 12396 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12396 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12396 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12396 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12396 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164257096468 + 0.011910655270 + (0.008585504608 : ℝ) *
        (1 + 2 * (0.284155653178 + 0.011910655270) / (0.560489483357 * 111.337325277734))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12396]

end BstLean.Part269.N12396

/-! The original eight local profiles supply actual 12396 moment certificates. -/
namespace BstLean.Part269.N12396
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12396 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12396 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12396 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053372390757 ∧
    0 ≤ bN 12396 BstLean.Part154.csC (groupTheta g) ∧ bN 12396 BstLean.Part154.csC (groupTheta g) ≤ 0.001415433043 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12396 12396 0.011
      (momentAllowance 12396 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12396 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12396 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12396 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12396 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12396 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231024654003 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12396 0.011
      (momentAllowance 12396 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12396 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12396
/-! The actual computed-centre upper energy formula at 12396. -/
namespace BstLean.Part269.N12396
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12396

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12396
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12396)
open BstLean.Part268 (cell12396)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086432585557
  | 2 => 0.087393979049
  | 3 => 0.088356440660
  | 4 => 0.089322046499
  | 5 => 0.090293283116
  | 6 => 0.091273105181
  | 7 => 0.092264997986
  | 8 => 0.093273044733
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12396 12396 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12396 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004098049004 + 0.003383255859 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S1.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12396

/-! Actual upper energy certificates on all 43 source endpoints at 12396. -/
namespace BstLean.Part269.N12396
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12396)
open BstLean.Part268 (cell12396)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12396 (gMinus 12396) (1 - (cell12396 i).lower) ≤ 1 ∧
    energyUpper 12396 (gMinus 12396) (BstLean.Part211.gPlus 12396)
      (finiteEnergy 12396 12396 0.011) (1 - (cell12396 i).lower) ≤
      (cell12396 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨10,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨11,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨12,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨13,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨14,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨15,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨16,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨17,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨18,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨19,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨20,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨21,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨22,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨23,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨24,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨25,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨26,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨27,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨28,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨29,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨30,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨31,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨32,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨33,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨34,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨35,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨36,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨37,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨38,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨39,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨40,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨41,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨42,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨43,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨44,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨45,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨46,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨47,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨48,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨49,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨50,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨51,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12396) (by norm_num)
        (q := 1 - (cell12396 ⟨52,by decide⟩).lower)
        (by norm_num [cell12396]) (by norm_num [cell12396])
      exact ⟨E.1,E.2.trans (by norm_num [cell12396])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12396

/-! Source-cell containment and simple scalar guards at 12396. -/
namespace BstLean.Part269.N12396
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12396)
open BstLean.Part268 (cell12396)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12396 ⟨10,by decide⟩).lower ∧ (cell12396 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12396 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12396 ⟨11,by decide⟩).lower ∧ (cell12396 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12396 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12396 ⟨12,by decide⟩).lower ∧ (cell12396 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12396 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12396 ⟨13,by decide⟩).lower ∧ (cell12396 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12396 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12396 ⟨14,by decide⟩).lower ∧ (cell12396 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12396 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12396 ⟨15,by decide⟩).lower ∧ (cell12396 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12396 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12396 ⟨16,by decide⟩).lower ∧ (cell12396 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12396 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12396 ⟨17,by decide⟩).lower ∧ (cell12396 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12396 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12396 ⟨18,by decide⟩).lower ∧ (cell12396 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12396 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12396 ⟨19,by decide⟩).lower ∧ (cell12396 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12396 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12396 ⟨20,by decide⟩).lower ∧ (cell12396 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12396 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12396 ⟨21,by decide⟩).lower ∧ (cell12396 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12396 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12396 ⟨22,by decide⟩).lower ∧ (cell12396 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12396 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12396 ⟨23,by decide⟩).lower ∧ (cell12396 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12396 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12396 ⟨24,by decide⟩).lower ∧ (cell12396 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12396 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12396 ⟨25,by decide⟩).lower ∧ (cell12396 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12396 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12396 ⟨26,by decide⟩).lower ∧ (cell12396 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12396 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12396 ⟨27,by decide⟩).lower ∧ (cell12396 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12396 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12396 ⟨28,by decide⟩).lower ∧ (cell12396 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12396 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12396 ⟨29,by decide⟩).lower ∧ (cell12396 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12396 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12396 ⟨30,by decide⟩).lower ∧ (cell12396 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12396 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12396 ⟨31,by decide⟩).lower ∧ (cell12396 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12396 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12396 ⟨32,by decide⟩).lower ∧ (cell12396 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12396 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12396 ⟨33,by decide⟩).lower ∧ (cell12396 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12396 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12396 ⟨34,by decide⟩).lower ∧ (cell12396 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12396 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12396 ⟨35,by decide⟩).lower ∧ (cell12396 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12396 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12396 ⟨36,by decide⟩).lower ∧ (cell12396 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12396 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12396 ⟨37,by decide⟩).lower ∧ (cell12396 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12396 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12396 ⟨38,by decide⟩).lower ∧ (cell12396 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12396 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12396 ⟨39,by decide⟩).lower ∧ (cell12396 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12396 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12396 ⟨40,by decide⟩).lower ∧ (cell12396 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12396 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12396 ⟨41,by decide⟩).lower ∧ (cell12396 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12396 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12396 ⟨42,by decide⟩).lower ∧ (cell12396 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12396 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12396 ⟨43,by decide⟩).lower ∧ (cell12396 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12396 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12396 ⟨44,by decide⟩).lower ∧ (cell12396 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12396 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12396 ⟨45,by decide⟩).lower ∧ (cell12396 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12396 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12396 ⟨46,by decide⟩).lower ∧ (cell12396 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12396 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12396 ⟨47,by decide⟩).lower ∧ (cell12396 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12396 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12396 ⟨48,by decide⟩).lower ∧ (cell12396 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12396 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12396 ⟨49,by decide⟩).lower ∧ (cell12396 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12396 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12396 ⟨50,by decide⟩).lower ∧ (cell12396 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12396 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12396 ⟨51,by decide⟩).lower ∧ (cell12396 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12396 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12396 ⟨52,by decide⟩).lower ∧ (cell12396 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12396 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12396 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12396 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12396,cell12396,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12396 i).lower ∧
    (cell12396 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12396 i).upper ≤ (0.532 : ℝ) ∧
    (cell12396 i).centre ≤ (0.1 : ℝ) ∧ (cell12396 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12396 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12396 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12396

/-! The local source numeric instances at 12396 have no network premises. -/
namespace BstLean.Part269.N12396
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12396)
open BstLean.Part268 (cell12396)

noncomputable def sourceNumerics12396 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12396 (cell12396 i)
      scalarRow12396.M scalarRow12396.H scalarRow12396.xi := by
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
    energy_allowance := scalarRow12396.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12396]
    centre_nonneg := (scalarRow12396.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12396])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12396
/-! Actual 12397 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12397
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12397 ≤ (1.036248065192 : ℝ) := by
  have hr : (111.341816044108 : ℝ) ≤ √(12397 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.341816044108 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12397 12397 (11 / 1000) ≤
    (0.008585158325 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12397) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.341816044108 : ℝ) ≤ √(12397 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12397)
  have hdiv : K / √(12397 : ℝ) ≤ K / 111.341816044108 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.341816044108 ≤ (0.008585158325 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12397.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12397 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12397 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12397 := gPlus_lower 12397
end BstLean.Part269.N12397

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12397
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036248065191 : ℝ) ≤ wn 12397 := by
  have hn : √(12397 : ℝ) ≤ 111.341816044109 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12397 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.341816044109 ≤ 2 / √(12397 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258146513 : ℝ) ≤ rhoBar 12397 BstLean.Part154.csC ∧
    rhoBar 12397 BstLean.Part154.csC ≤ 0.000258146912 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036248065191 : ℝ) / (1.295212 * 12397) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036248065192 : ℝ) / (1.29521 * 12397) := by gcongr
      _ ≤ (0.000258146912 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12397 BstLean.Part154.csC) ≤ 0.001032654288 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12397 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12397 BstLean.Part154.csC) (piBar (rhoBar 12397 BstLean.Part154.csC)) ≤ 0.000197174581 ∧
    cc1 (rhoBar 12397 BstLean.Part154.csC) (piBar (rhoBar 12397 BstLean.Part154.csC)) ≤ 0.000125463448 ∧
    cc2 (rhoBar 12397 BstLean.Part154.csC) ≤ 0.000072832436 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12397 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12397 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12397 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12397 BstLean.Part154.csC * nuR (rhoBar 12397 BstLean.Part154.csC)) ≤ 0.000516310484 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258146912 : ℝ) * 0.001032654288 := by gcongr
      _ ≤ (0.000516310484 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12397 BstLean.Part154.csC) * nuR (rhoBar 12397 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001032654288 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12397 BstLean.Part154.csC) * rhoBar 12397 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258146912 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258146912 / 2 + 0.399 * 0.001032654288 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197174581 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516310484 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125463448 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258146912 / 1.414213562 := by gcongr
      _ ≤ (0.000072832436 : ℝ) := by norm_num

end BstLean.Part269.N12397

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12397
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12397 BstLean.Part154.csC) (piBar (rhoBar 12397 BstLean.Part154.csC)) ≤ 1.67895E-7 := by
  have hr0 : 0 ≤ rhoBar 12397 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12397 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12397 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12397 BstLean.Part154.csC) (piBar (rhoBar 12397 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12397 BstLean.Part154.csC) (piBar (rhoBar 12397 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12397 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197174581 : ℝ) ^ 2 + 0.000125463448 ^ 2 + 3 * 0.000072832436 ^ 2 +
        2 * 0.797885 * 0.000197174581 * 0.000125463448 + 2 * 0.000197174581 * 0.000072832436 +
        4 * 0.797885 * 0.000125463448 * 0.000072832436 := by gcongr
    _ ≤ (1.67895E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12397 BstLean.Part154.csC Θ ≤ 0.002695846896 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12397 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12397 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12397 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12397 BstLean.Part154.csC) (piBar (rhoBar 12397 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12397 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036248065192 * 1.67895E-7 / (0.000258146513 : ℝ) := by gcongr
    _ ≤ 0.002695846896 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12397 BstLean.Part154.csC Θ ≤ 0.002992446736 + 0.000681194091 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12397 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12397 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12397 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036248065192 : ℝ) * ((2 * Θ * 0.000258146912 +
        (6863 / 10000) * 0.000258146912 * 12397 * 0.001032654288) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002992446736 + 0.000681194091 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12397 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12397 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12397 0.011 Θ ∧ gammaRatio 12397 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12397 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036248065192 : ℝ) * 0.525 / ((1 - 0.011) * 12397) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12397 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12397 0.011 Θ) :=
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
    badAllowance 12397 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12397 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12397 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12397 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12397 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12397 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12397 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12397 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12397 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12397 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12397 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036248065192 : ℝ) * 12397 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12397 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004092446736 + 0.003377040987 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12397

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12397
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12397 BstLean.Part154.csC) (piBar (rhoBar 12397 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12397 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12397 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12397 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12397 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12397 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12397 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12397 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12397 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12397 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12397 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12397 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12397 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12397 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12397 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053128832721 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12397) ≤ 0.010725867635 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12397 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036248065192)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010725867635 + 2 * 0.737676 / 12397) := by gcongr
    _ ≤ (0.053128832721 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12397 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12397

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12397
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489530821 : ℝ) ≤ plow 12397 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12397) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053371993255)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415319621) : eMP 12397 0.011 xi bn ≤ 0.001218089668 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12397 : ℝ) * (1 - 0.011))) ≤ 0.000602206970 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001415319621 / (12397 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602206970 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602206970 : ℝ) + 3.141593 * 0.053371993255 / (12397 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001218089668 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053371993255)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415319621) : PiBarMP 12397 12 0.011 xi bn ≤ 0.163231904231 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12397 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037620733925 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.727742684478 : ℝ) ≤ √((12397 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.341816044108 : ℝ) ≤ √(12397 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12397) ≤ 0.125131857534 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037620733925 + 0.053371993255 * 1.772454 / (2 * (110.727742684478 : ℝ))) * (1 + 0.001218089668) +
        8 / (12397 * 111.341816044108) + 0.125131857534 := by gcongr
    _ ≤ (0.163231904231 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053371993255)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415319621) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284152626420) :
    parallelOracle 12397 0.011 xi bn cd ≤ 0.164250441294 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12397 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12397 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489530821 : ℝ) ≤ plow 12397 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.341816044108 : ℝ) ≤ √(12397 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284152626420 : ℝ) / (2 * 0.560489530821 * 111.341816044108)) * 0.163231904231 +
        0.284152626420 ^ 2 / (2 * 0.560489530821 * 111.341816044108) := by gcongr
    _ ≤ (0.164250441294 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053371993255) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415319621)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284152626420) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12397 12397 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489530821 : ℝ) ≤ plow 12397 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.341816044108 : ℝ) ≤ √(12397 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12397 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12397 Θ 1.22 ≤ 0.011910174876 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.341816044108 := by gcongr <;> linarith
      _ ≤ (0.011910174876 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12397 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12397 12397 0.011 ≤ 0.008585158325 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12397 12397 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12397 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12397 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12397 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12397 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164250441294 + 0.011910174876 + (0.008585158325 : ℝ) *
        (1 + 2 * (0.284152626420 + 0.011910174876) / (0.560489530821 * 111.341816044108))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12397]

end BstLean.Part269.N12397

/-! The original eight local profiles supply actual 12397 moment certificates. -/
namespace BstLean.Part269.N12397
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12397 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12397 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12397 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053371993255 ∧
    0 ≤ bN 12397 BstLean.Part154.csC (groupTheta g) ∧ bN 12397 BstLean.Part154.csC (groupTheta g) ≤ 0.001415319621 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12397 12397 0.011
      (momentAllowance 12397 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12397 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12397 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12397 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12397 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12397 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231023793699 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12397 0.011
      (momentAllowance 12397 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12397 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12397
/-! The actual computed-centre upper energy formula at 12397. -/
namespace BstLean.Part269.N12397
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12397

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12397
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12397)
open BstLean.Part268 (cell12397)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086429282391
  | 2 => 0.087390605739
  | 3 => 0.088352985512
  | 4 => 0.089318495248
  | 5 => 0.090289618494
  | 6 => 0.091269306433
  | 7 => 0.092261040334
  | 8 => 0.093268898793
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12397 12397 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12397 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004098049004 + 0.003383255859 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S1.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12397

/-! Actual upper energy certificates on all 43 source endpoints at 12397. -/
namespace BstLean.Part269.N12397
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12397)
open BstLean.Part268 (cell12397)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12397 (gMinus 12397) (1 - (cell12397 i).lower) ≤ 1 ∧
    energyUpper 12397 (gMinus 12397) (BstLean.Part211.gPlus 12397)
      (finiteEnergy 12397 12397 0.011) (1 - (cell12397 i).lower) ≤
      (cell12397 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨10,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨11,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨12,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨13,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨14,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨15,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨16,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨17,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨18,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨19,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨20,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨21,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨22,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨23,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨24,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨25,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨26,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨27,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨28,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨29,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨30,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨31,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨32,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨33,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨34,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨35,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨36,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨37,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨38,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨39,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨40,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨41,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨42,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨43,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨44,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨45,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨46,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨47,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨48,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨49,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨50,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨51,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12397) (by norm_num)
        (q := 1 - (cell12397 ⟨52,by decide⟩).lower)
        (by norm_num [cell12397]) (by norm_num [cell12397])
      exact ⟨E.1,E.2.trans (by norm_num [cell12397])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12397

/-! Source-cell containment and simple scalar guards at 12397. -/
namespace BstLean.Part269.N12397
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12397)
open BstLean.Part268 (cell12397)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12397 ⟨10,by decide⟩).lower ∧ (cell12397 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12397 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12397 ⟨11,by decide⟩).lower ∧ (cell12397 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12397 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12397 ⟨12,by decide⟩).lower ∧ (cell12397 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12397 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12397 ⟨13,by decide⟩).lower ∧ (cell12397 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12397 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12397 ⟨14,by decide⟩).lower ∧ (cell12397 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12397 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12397 ⟨15,by decide⟩).lower ∧ (cell12397 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12397 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12397 ⟨16,by decide⟩).lower ∧ (cell12397 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12397 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12397 ⟨17,by decide⟩).lower ∧ (cell12397 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12397 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12397 ⟨18,by decide⟩).lower ∧ (cell12397 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12397 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12397 ⟨19,by decide⟩).lower ∧ (cell12397 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12397 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12397 ⟨20,by decide⟩).lower ∧ (cell12397 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12397 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12397 ⟨21,by decide⟩).lower ∧ (cell12397 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12397 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12397 ⟨22,by decide⟩).lower ∧ (cell12397 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12397 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12397 ⟨23,by decide⟩).lower ∧ (cell12397 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12397 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12397 ⟨24,by decide⟩).lower ∧ (cell12397 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12397 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12397 ⟨25,by decide⟩).lower ∧ (cell12397 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12397 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12397 ⟨26,by decide⟩).lower ∧ (cell12397 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12397 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12397 ⟨27,by decide⟩).lower ∧ (cell12397 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12397 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12397 ⟨28,by decide⟩).lower ∧ (cell12397 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12397 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12397 ⟨29,by decide⟩).lower ∧ (cell12397 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12397 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12397 ⟨30,by decide⟩).lower ∧ (cell12397 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12397 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12397 ⟨31,by decide⟩).lower ∧ (cell12397 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12397 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12397 ⟨32,by decide⟩).lower ∧ (cell12397 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12397 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12397 ⟨33,by decide⟩).lower ∧ (cell12397 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12397 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12397 ⟨34,by decide⟩).lower ∧ (cell12397 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12397 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12397 ⟨35,by decide⟩).lower ∧ (cell12397 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12397 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12397 ⟨36,by decide⟩).lower ∧ (cell12397 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12397 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12397 ⟨37,by decide⟩).lower ∧ (cell12397 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12397 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12397 ⟨38,by decide⟩).lower ∧ (cell12397 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12397 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12397 ⟨39,by decide⟩).lower ∧ (cell12397 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12397 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12397 ⟨40,by decide⟩).lower ∧ (cell12397 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12397 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12397 ⟨41,by decide⟩).lower ∧ (cell12397 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12397 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12397 ⟨42,by decide⟩).lower ∧ (cell12397 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12397 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12397 ⟨43,by decide⟩).lower ∧ (cell12397 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12397 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12397 ⟨44,by decide⟩).lower ∧ (cell12397 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12397 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12397 ⟨45,by decide⟩).lower ∧ (cell12397 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12397 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12397 ⟨46,by decide⟩).lower ∧ (cell12397 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12397 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12397 ⟨47,by decide⟩).lower ∧ (cell12397 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12397 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12397 ⟨48,by decide⟩).lower ∧ (cell12397 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12397 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12397 ⟨49,by decide⟩).lower ∧ (cell12397 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12397 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12397 ⟨50,by decide⟩).lower ∧ (cell12397 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12397 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12397 ⟨51,by decide⟩).lower ∧ (cell12397 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12397 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12397 ⟨52,by decide⟩).lower ∧ (cell12397 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12397 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12397 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12397 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12397,cell12397,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12397 i).lower ∧
    (cell12397 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12397 i).upper ≤ (0.532 : ℝ) ∧
    (cell12397 i).centre ≤ (0.1 : ℝ) ∧ (cell12397 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12397 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12397 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12397

/-! The local source numeric instances at 12397 have no network premises. -/
namespace BstLean.Part269.N12397
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12397)
open BstLean.Part268 (cell12397)

noncomputable def sourceNumerics12397 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12397 (cell12397 i)
      scalarRow12397.M scalarRow12397.H scalarRow12397.xi := by
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
    energy_allowance := scalarRow12397.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12397]
    centre_nonneg := (scalarRow12397.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12397])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12397
/-! Actual 12398 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12398
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12398 ≤ (1.036246590299 : ℝ) := by
  have hr : (111.346306629362 : ℝ) ≤ √(12398 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.346306629362 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12398 12398 (11 / 1000) ≤
    (0.008584812084 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12398) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.346306629362 : ℝ) ≤ √(12398 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12398)
  have hdiv : K / √(12398 : ℝ) ≤ K / 111.346306629362 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.346306629362 ≤ (0.008584812084 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12398.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12398 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12398 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12398 := gPlus_lower 12398
end BstLean.Part269.N12398

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12398
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036246590298 : ℝ) ≤ wn 12398 := by
  have hn : √(12398 : ℝ) ≤ 111.346306629363 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12398 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.346306629363 ≤ 2 / √(12398 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258125324 : ℝ) ≤ rhoBar 12398 BstLean.Part154.csC ∧
    rhoBar 12398 BstLean.Part154.csC ≤ 0.000258125723 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036246590298 : ℝ) / (1.295212 * 12398) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036246590299 : ℝ) / (1.29521 * 12398) := by gcongr
      _ ≤ (0.000258125723 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12398 BstLean.Part154.csC) ≤ 0.001032569521 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12398 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12398 BstLean.Part154.csC) (piBar (rhoBar 12398 BstLean.Part154.csC)) ≤ 0.000197158396 ∧
    cc1 (rhoBar 12398 BstLean.Part154.csC) (piBar (rhoBar 12398 BstLean.Part154.csC)) ≤ 0.000125453150 ∧
    cc2 (rhoBar 12398 BstLean.Part154.csC) ≤ 0.000072826458 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12398 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12398 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12398 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12398 BstLean.Part154.csC * nuR (rhoBar 12398 BstLean.Part154.csC)) ≤ 0.000516268103 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258125723 : ℝ) * 0.001032569521 := by gcongr
      _ ≤ (0.000516268103 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12398 BstLean.Part154.csC) * nuR (rhoBar 12398 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001032569521 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12398 BstLean.Part154.csC) * rhoBar 12398 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258125723 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258125723 / 2 + 0.399 * 0.001032569521 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197158396 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516268103 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125453150 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258125723 / 1.414213562 := by gcongr
      _ ≤ (0.000072826458 : ℝ) := by norm_num

end BstLean.Part269.N12398

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12398
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12398 BstLean.Part154.csC) (piBar (rhoBar 12398 BstLean.Part154.csC)) ≤ 1.67867E-7 := by
  have hr0 : 0 ≤ rhoBar 12398 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12398 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12398 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12398 BstLean.Part154.csC) (piBar (rhoBar 12398 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12398 BstLean.Part154.csC) (piBar (rhoBar 12398 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12398 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197158396 : ℝ) ^ 2 + 0.000125453150 ^ 2 + 3 * 0.000072826458 ^ 2 +
        2 * 0.797885 * 0.000197158396 * 0.000125453150 + 2 * 0.000197158396 * 0.000072826458 +
        4 * 0.797885 * 0.000125453150 * 0.000072826458 := by gcongr
    _ ≤ (1.67867E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12398 BstLean.Part154.csC Θ ≤ 0.002695614730 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12398 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12398 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12398 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12398 BstLean.Part154.csC) (piBar (rhoBar 12398 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12398 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036246590299 * 1.67867E-7 / (0.000258125324 : ℝ) := by gcongr
    _ ≤ 0.002695614730 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12398 BstLean.Part154.csC Θ ≤ 0.002992192579 + 0.000681137208 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12398 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12398 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12398 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036246590299 : ℝ) * ((2 * Θ * 0.000258125723 +
        (6863 / 10000) * 0.000258125723 * 12398 * 0.001032569521) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002992192579 + 0.000681137208 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12398 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12398 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12398 0.011 Θ ∧ gammaRatio 12398 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12398 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036246590299 : ℝ) * 0.525 / ((1 - 0.011) * 12398) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12398 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12398 0.011 Θ) :=
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
    badAllowance 12398 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12398 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12398 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12398 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12398 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12398 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12398 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12398 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12398 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12398 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12398 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036246590299 : ℝ) * 12398 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12398 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004092192579 + 0.003376751938 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12398

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12398
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12398 BstLean.Part154.csC) (piBar (rhoBar 12398 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12398 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12398 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12398 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12398 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12398 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12398 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12398 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12398 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12398 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12398 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12398 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12398 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12398 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12398 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053126666529 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12398) ≤ 0.010725435062 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12398 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036246590299)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010725435062 + 2 * 0.737676 / 12398) := by gcongr
    _ ≤ (0.053126666529 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12398 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12398

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12398
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489578278 : ℝ) ≤ plow 12398 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12398) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053371587347)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415197734) : eMP 12398 0.011 xi bn ≤ 0.001217988027 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12398 : ℝ) * (1 - 0.011))) ≤ 0.000602156753 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001415197734 / (12398 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602156753 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602156753 : ℝ) + 3.141593 * 0.053371587347 / (12398 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001217988027 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053371587347)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415197734) : PiBarMP 12398 12 0.011 xi bn ≤ 0.163225210653 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12398 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037619113945 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.732208503217 : ℝ) ≤ √((12398 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.346306629362 : ℝ) ≤ √(12398 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12398) ≤ 0.125126810979 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037619113945 + 0.053371587347 * 1.772454 / (2 * (110.732208503217 : ℝ))) * (1 + 0.001217988027) +
        8 / (12398 * 111.346306629362) + 0.125126810979 := by gcongr
    _ ≤ (0.163225210653 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053371587347)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415197734) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284149581728) :
    parallelOracle 12398 0.011 xi bn cd ≤ 0.164243673469 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12398 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12398 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489578278 : ℝ) ≤ plow 12398 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.346306629362 : ℝ) ≤ √(12398 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284149581728 : ℝ) / (2 * 0.560489578278 * 111.346306629362)) * 0.163225210653 +
        0.284149581728 ^ 2 / (2 * 0.560489578278 * 111.346306629362) := by gcongr
    _ ≤ (0.164243673469 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053371587347) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415197734)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284149581728) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12398 12398 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489578278 : ℝ) ≤ plow 12398 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.346306629362 : ℝ) ≤ √(12398 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12398 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12398 Θ 1.22 ≤ 0.011909694539 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.346306629362 := by gcongr <;> linarith
      _ ≤ (0.011909694539 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12398 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12398 12398 0.011 ≤ 0.008584812084 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12398 12398 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12398 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12398 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12398 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12398 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164243673469 + 0.011909694539 + (0.008584812084 : ℝ) *
        (1 + 2 * (0.284149581728 + 0.011909694539) / (0.560489578278 * 111.346306629362))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12398]

end BstLean.Part269.N12398

/-! The original eight local profiles supply actual 12398 moment certificates. -/
namespace BstLean.Part269.N12398
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12398 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12398 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12398 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053371587347 ∧
    0 ≤ bN 12398 BstLean.Part154.csC (groupTheta g) ∧ bN 12398 BstLean.Part154.csC (groupTheta g) ≤ 0.001415197734 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12398 12398 0.011
      (momentAllowance 12398 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12398 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12398 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12398 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12398 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12398 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231022915199 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12398 0.011
      (momentAllowance 12398 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12398 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12398
/-! The actual computed-centre upper energy formula at 12398. -/
namespace BstLean.Part269.N12398
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12398

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12398
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12398)
open BstLean.Part268 (cell12398)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086425980717
  | 2 => 0.087387233986
  | 3 => 0.088349532003
  | 4 => 0.089314945736
  | 5 => 0.090285955733
  | 6 => 0.091265509693
  | 7 => 0.092257084868
  | 8 => 0.093264755251
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12398 12398 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12398 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004098049004 + 0.003383255859 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S1.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12398

/-! Actual upper energy certificates on all 43 source endpoints at 12398. -/
namespace BstLean.Part269.N12398
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12398)
open BstLean.Part268 (cell12398)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12398 (gMinus 12398) (1 - (cell12398 i).lower) ≤ 1 ∧
    energyUpper 12398 (gMinus 12398) (BstLean.Part211.gPlus 12398)
      (finiteEnergy 12398 12398 0.011) (1 - (cell12398 i).lower) ≤
      (cell12398 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨10,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨11,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨12,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨13,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨14,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨15,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨16,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨17,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨18,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨19,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨20,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨21,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨22,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨23,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨24,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨25,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨26,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨27,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨28,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨29,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨30,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨31,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨32,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨33,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨34,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨35,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨36,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨37,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨38,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨39,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨40,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨41,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨42,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨43,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨44,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨45,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨46,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨47,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨48,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨49,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨50,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨51,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12398) (by norm_num)
        (q := 1 - (cell12398 ⟨52,by decide⟩).lower)
        (by norm_num [cell12398]) (by norm_num [cell12398])
      exact ⟨E.1,E.2.trans (by norm_num [cell12398])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12398

/-! Source-cell containment and simple scalar guards at 12398. -/
namespace BstLean.Part269.N12398
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12398)
open BstLean.Part268 (cell12398)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12398 ⟨10,by decide⟩).lower ∧ (cell12398 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12398 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12398 ⟨11,by decide⟩).lower ∧ (cell12398 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12398 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12398 ⟨12,by decide⟩).lower ∧ (cell12398 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12398 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12398 ⟨13,by decide⟩).lower ∧ (cell12398 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12398 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12398 ⟨14,by decide⟩).lower ∧ (cell12398 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12398 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12398 ⟨15,by decide⟩).lower ∧ (cell12398 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12398 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12398 ⟨16,by decide⟩).lower ∧ (cell12398 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12398 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12398 ⟨17,by decide⟩).lower ∧ (cell12398 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12398 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12398 ⟨18,by decide⟩).lower ∧ (cell12398 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12398 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12398 ⟨19,by decide⟩).lower ∧ (cell12398 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12398 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12398 ⟨20,by decide⟩).lower ∧ (cell12398 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12398 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12398 ⟨21,by decide⟩).lower ∧ (cell12398 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12398 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12398 ⟨22,by decide⟩).lower ∧ (cell12398 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12398 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12398 ⟨23,by decide⟩).lower ∧ (cell12398 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12398 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12398 ⟨24,by decide⟩).lower ∧ (cell12398 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12398 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12398 ⟨25,by decide⟩).lower ∧ (cell12398 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12398 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12398 ⟨26,by decide⟩).lower ∧ (cell12398 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12398 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12398 ⟨27,by decide⟩).lower ∧ (cell12398 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12398 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12398 ⟨28,by decide⟩).lower ∧ (cell12398 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12398 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12398 ⟨29,by decide⟩).lower ∧ (cell12398 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12398 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12398 ⟨30,by decide⟩).lower ∧ (cell12398 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12398 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12398 ⟨31,by decide⟩).lower ∧ (cell12398 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12398 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12398 ⟨32,by decide⟩).lower ∧ (cell12398 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12398 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12398 ⟨33,by decide⟩).lower ∧ (cell12398 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12398 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12398 ⟨34,by decide⟩).lower ∧ (cell12398 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12398 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12398 ⟨35,by decide⟩).lower ∧ (cell12398 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12398 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12398 ⟨36,by decide⟩).lower ∧ (cell12398 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12398 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12398 ⟨37,by decide⟩).lower ∧ (cell12398 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12398 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12398 ⟨38,by decide⟩).lower ∧ (cell12398 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12398 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12398 ⟨39,by decide⟩).lower ∧ (cell12398 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12398 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12398 ⟨40,by decide⟩).lower ∧ (cell12398 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12398 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12398 ⟨41,by decide⟩).lower ∧ (cell12398 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12398 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12398 ⟨42,by decide⟩).lower ∧ (cell12398 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12398 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12398 ⟨43,by decide⟩).lower ∧ (cell12398 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12398 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12398 ⟨44,by decide⟩).lower ∧ (cell12398 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12398 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12398 ⟨45,by decide⟩).lower ∧ (cell12398 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12398 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12398 ⟨46,by decide⟩).lower ∧ (cell12398 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12398 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12398 ⟨47,by decide⟩).lower ∧ (cell12398 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12398 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12398 ⟨48,by decide⟩).lower ∧ (cell12398 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12398 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12398 ⟨49,by decide⟩).lower ∧ (cell12398 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12398 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12398 ⟨50,by decide⟩).lower ∧ (cell12398 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12398 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12398 ⟨51,by decide⟩).lower ∧ (cell12398 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12398 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12398 ⟨52,by decide⟩).lower ∧ (cell12398 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12398 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12398 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12398 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12398,cell12398,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12398 i).lower ∧
    (cell12398 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12398 i).upper ≤ (0.532 : ℝ) ∧
    (cell12398 i).centre ≤ (0.1 : ℝ) ∧ (cell12398 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12398 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12398 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12398

/-! The local source numeric instances at 12398 have no network premises. -/
namespace BstLean.Part269.N12398
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12398)
open BstLean.Part268 (cell12398)

noncomputable def sourceNumerics12398 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12398 (cell12398 i)
      scalarRow12398.M scalarRow12398.H scalarRow12398.xi := by
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
    energy_allowance := scalarRow12398.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12398]
    centre_nonneg := (scalarRow12398.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12398])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12398
/-! Actual 12399 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12399
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12399 ≤ (1.036245115585 : ℝ) := by
  have hr : (111.350797033519 : ℝ) ≤ √(12399 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.350797033519 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12399 12399 (11 / 1000) ≤
    (0.008584465884 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12399) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.350797033519 : ℝ) ≤ √(12399 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12399)
  have hdiv : K / √(12399 : ℝ) ≤ K / 111.350797033519 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.350797033519 ≤ (0.008584465884 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12399.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12399 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12399 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12399 := gPlus_lower 12399
end BstLean.Part269.N12399

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12399
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036245115584 : ℝ) ≤ wn 12399 := by
  have hn : √(12399 : ℝ) ≤ 111.350797033520 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12399 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.350797033520 ≤ 2 / √(12399 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258104138 : ℝ) ≤ rhoBar 12399 BstLean.Part154.csC ∧
    rhoBar 12399 BstLean.Part154.csC ≤ 0.000258104538 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036245115584 : ℝ) / (1.295212 * 12399) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036245115585 : ℝ) / (1.29521 * 12399) := by gcongr
      _ ≤ (0.000258104538 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12399 BstLean.Part154.csC) ≤ 0.001032484770 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12399 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12399 BstLean.Part154.csC) (piBar (rhoBar 12399 BstLean.Part154.csC)) ≤ 0.000197142214 ∧
    cc1 (rhoBar 12399 BstLean.Part154.csC) (piBar (rhoBar 12399 BstLean.Part154.csC)) ≤ 0.000125442853 ∧
    cc2 (rhoBar 12399 BstLean.Part154.csC) ≤ 0.000072820481 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12399 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12399 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12399 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12399 BstLean.Part154.csC * nuR (rhoBar 12399 BstLean.Part154.csC)) ≤ 0.000516225731 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258104538 : ℝ) * 0.001032484770 := by gcongr
      _ ≤ (0.000516225731 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12399 BstLean.Part154.csC) * nuR (rhoBar 12399 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001032484770 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12399 BstLean.Part154.csC) * rhoBar 12399 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258104538 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258104538 / 2 + 0.399 * 0.001032484770 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197142214 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516225731 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125442853 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258104538 / 1.414213562 := by gcongr
      _ ≤ (0.000072820481 : ℝ) := by norm_num

end BstLean.Part269.N12399

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12399
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12399 BstLean.Part154.csC) (piBar (rhoBar 12399 BstLean.Part154.csC)) ≤ 1.67840E-7 := by
  have hr0 : 0 ≤ rhoBar 12399 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12399 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12399 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12399 BstLean.Part154.csC) (piBar (rhoBar 12399 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12399 BstLean.Part154.csC) (piBar (rhoBar 12399 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12399 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197142214 : ℝ) ^ 2 + 0.000125442853 ^ 2 + 3 * 0.000072820481 ^ 2 +
        2 * 0.797885 * 0.000197142214 * 0.000125442853 + 2 * 0.000197142214 * 0.000072820481 +
        4 * 0.797885 * 0.000125442853 * 0.000072820481 := by gcongr
    _ ≤ (1.67840E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12399 BstLean.Part154.csC Θ ≤ 0.002695398556 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12399 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12399 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12399 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12399 BstLean.Part154.csC) (piBar (rhoBar 12399 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12399 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036245115585 * 1.67840E-7 / (0.000258104138 : ℝ) := by gcongr
    _ ≤ 0.002695398556 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12399 BstLean.Part154.csC Θ ≤ 0.002991938478 + 0.000681080336 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12399 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12399 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12399 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036245115585 : ℝ) * ((2 * Θ * 0.000258104538 +
        (6863 / 10000) * 0.000258104538 * 12399 * 0.001032484770) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002991938478 + 0.000681080336 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12399 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12399 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12399 0.011 Θ ∧ gammaRatio 12399 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12399 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036245115585 : ℝ) * 0.525 / ((1 - 0.011) * 12399) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12399 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12399 0.011 Θ) :=
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
    badAllowance 12399 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12399 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12399 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12399 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12399 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12399 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12399 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12399 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12399 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12399 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12399 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036245115585 : ℝ) * 12399 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12399 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004091938478 + 0.003376478892 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12399

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12399
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12399 BstLean.Part154.csC) (piBar (rhoBar 12399 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12399 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12399 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12399 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12399 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12399 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12399 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12399 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12399 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12399 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12399 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12399 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12399 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12399 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12399 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053124500600 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12399) ≤ 0.010725002541 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12399 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036245115585)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010725002541 + 2 * 0.737676 / 12399) := by gcongr
    _ ≤ (0.053124500600 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12399 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12399

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12399
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489625727 : ℝ) ≤ plow 12399 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12399) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053371189897)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415084242) : eMP 12399 0.011 xi bn ≤ 0.001217889967 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12399 : ℝ) * (1 - 0.011))) ≤ 0.000602108325 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001415084242 / (12399 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602108325 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602108325 : ℝ) + 3.141593 * 0.053371189897 / (12399 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001217889967 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053371189897)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415084242) : PiBarMP 12399 12 0.011 xi bn ≤ 0.163218629543 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12399 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037617605480 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.736674141857 : ℝ) ≤ √((12399 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.350797033519 : ℝ) ≤ √(12399 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12399) ≤ 0.125121765034 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037617605480 + 0.053371189897 * 1.772454 / (2 * (110.736674141857 : ℝ))) * (1 + 0.001217889967) +
        8 / (12399 * 111.350797033519) + 0.125121765034 := by gcongr
    _ ≤ (0.163218629543 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053371189897)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415084242) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284146555602) :
    parallelOracle 12399 0.011 xi bn cd ≤ 0.164237018486 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12399 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12399 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489625727 : ℝ) ≤ plow 12399 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.350797033519 : ℝ) ≤ √(12399 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284146555602 : ℝ) / (2 * 0.560489625727 * 111.350797033519)) * 0.163218629543 +
        0.284146555602 ^ 2 / (2 * 0.560489625727 * 111.350797033519) := by gcongr
    _ ≤ (0.164237018486 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053371189897) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001415084242)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284146555602) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12399 12399 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489625727 : ℝ) ≤ plow 12399 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.350797033519 : ℝ) ≤ √(12399 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12399 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12399 Θ 1.22 ≤ 0.011909214261 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.350797033519 := by gcongr <;> linarith
      _ ≤ (0.011909214261 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12399 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12399 12399 0.011 ≤ 0.008584465884 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12399 12399 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12399 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12399 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12399 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12399 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164237018486 + 0.011909214261 + (0.008584465884 : ℝ) *
        (1 + 2 * (0.284146555602 + 0.011909214261) / (0.560489625727 * 111.350797033519))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12399]

end BstLean.Part269.N12399

/-! The original eight local profiles supply actual 12399 moment certificates. -/
namespace BstLean.Part269.N12399
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12399 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12399 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12399 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053371189897 ∧
    0 ≤ bN 12399 BstLean.Part154.csC (groupTheta g) ∧ bN 12399 BstLean.Part154.csC (groupTheta g) ≤ 0.001415084242 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12399 12399 0.011
      (momentAllowance 12399 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12399 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12399 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12399 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12399 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12399 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231022055002 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12399 0.011
      (momentAllowance 12399 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12399 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12399
/-! The actual computed-centre upper energy formula at 12399. -/
namespace BstLean.Part269.N12399
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12399

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12399
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12399)
open BstLean.Part268 (cell12399)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086422680532
  | 2 => 0.087383863788
  | 3 => 0.088346080131
  | 4 => 0.089311397962
  | 5 => 0.090282294831
  | 6 => 0.091261714958
  | 7 => 0.092253131586
  | 8 => 0.093260614104
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12399 12399 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12399 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004098049004 + 0.003383255859 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S1.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S1.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12399

/-! Actual upper energy certificates on all 43 source endpoints at 12399. -/
namespace BstLean.Part269.N12399
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12399)
open BstLean.Part268 (cell12399)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12399 (gMinus 12399) (1 - (cell12399 i).lower) ≤ 1 ∧
    energyUpper 12399 (gMinus 12399) (BstLean.Part211.gPlus 12399)
      (finiteEnergy 12399 12399 0.011) (1 - (cell12399 i).lower) ≤
      (cell12399 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨10,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨11,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨12,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨13,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨14,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨15,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨16,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨17,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨18,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨19,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨20,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨21,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨22,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨23,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨24,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨25,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨26,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨27,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨28,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨29,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨30,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨31,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨32,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨33,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨34,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨35,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨36,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨37,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨38,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨39,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨40,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨41,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨42,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨43,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨44,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨45,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨46,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨47,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨48,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨49,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨50,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨51,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12399) (by norm_num)
        (q := 1 - (cell12399 ⟨52,by decide⟩).lower)
        (by norm_num [cell12399]) (by norm_num [cell12399])
      exact ⟨E.1,E.2.trans (by norm_num [cell12399])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12399

/-! Source-cell containment and simple scalar guards at 12399. -/
namespace BstLean.Part269.N12399
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12399)
open BstLean.Part268 (cell12399)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12399 ⟨10,by decide⟩).lower ∧ (cell12399 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12399 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12399 ⟨11,by decide⟩).lower ∧ (cell12399 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12399 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12399 ⟨12,by decide⟩).lower ∧ (cell12399 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12399 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12399 ⟨13,by decide⟩).lower ∧ (cell12399 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12399 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12399 ⟨14,by decide⟩).lower ∧ (cell12399 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12399 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12399 ⟨15,by decide⟩).lower ∧ (cell12399 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12399 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12399 ⟨16,by decide⟩).lower ∧ (cell12399 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12399 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12399 ⟨17,by decide⟩).lower ∧ (cell12399 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12399 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12399 ⟨18,by decide⟩).lower ∧ (cell12399 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12399 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12399 ⟨19,by decide⟩).lower ∧ (cell12399 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12399 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12399 ⟨20,by decide⟩).lower ∧ (cell12399 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12399 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12399 ⟨21,by decide⟩).lower ∧ (cell12399 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12399 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12399 ⟨22,by decide⟩).lower ∧ (cell12399 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12399 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12399 ⟨23,by decide⟩).lower ∧ (cell12399 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12399 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12399 ⟨24,by decide⟩).lower ∧ (cell12399 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12399 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12399 ⟨25,by decide⟩).lower ∧ (cell12399 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12399 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12399 ⟨26,by decide⟩).lower ∧ (cell12399 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12399 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12399 ⟨27,by decide⟩).lower ∧ (cell12399 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12399 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12399 ⟨28,by decide⟩).lower ∧ (cell12399 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12399 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12399 ⟨29,by decide⟩).lower ∧ (cell12399 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12399 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12399 ⟨30,by decide⟩).lower ∧ (cell12399 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12399 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12399 ⟨31,by decide⟩).lower ∧ (cell12399 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12399 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12399 ⟨32,by decide⟩).lower ∧ (cell12399 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12399 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12399 ⟨33,by decide⟩).lower ∧ (cell12399 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12399 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12399 ⟨34,by decide⟩).lower ∧ (cell12399 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12399 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12399 ⟨35,by decide⟩).lower ∧ (cell12399 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12399 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12399 ⟨36,by decide⟩).lower ∧ (cell12399 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12399 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12399 ⟨37,by decide⟩).lower ∧ (cell12399 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12399 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12399 ⟨38,by decide⟩).lower ∧ (cell12399 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12399 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12399 ⟨39,by decide⟩).lower ∧ (cell12399 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12399 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12399 ⟨40,by decide⟩).lower ∧ (cell12399 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12399 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12399 ⟨41,by decide⟩).lower ∧ (cell12399 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12399 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12399 ⟨42,by decide⟩).lower ∧ (cell12399 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12399 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12399 ⟨43,by decide⟩).lower ∧ (cell12399 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12399 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12399 ⟨44,by decide⟩).lower ∧ (cell12399 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12399 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12399 ⟨45,by decide⟩).lower ∧ (cell12399 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12399 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12399 ⟨46,by decide⟩).lower ∧ (cell12399 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12399 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12399 ⟨47,by decide⟩).lower ∧ (cell12399 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12399 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12399 ⟨48,by decide⟩).lower ∧ (cell12399 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12399 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12399 ⟨49,by decide⟩).lower ∧ (cell12399 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12399 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12399 ⟨50,by decide⟩).lower ∧ (cell12399 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12399 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12399 ⟨51,by decide⟩).lower ∧ (cell12399 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12399 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12399 ⟨52,by decide⟩).lower ∧ (cell12399 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12399 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12399 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12399 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12399,cell12399,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12399 i).lower ∧
    (cell12399 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12399 i).upper ≤ (0.532 : ℝ) ∧
    (cell12399 i).centre ≤ (0.1 : ℝ) ∧ (cell12399 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12399 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12399 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12399

/-! The local source numeric instances at 12399 have no network premises. -/
namespace BstLean.Part269.N12399
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12399)
open BstLean.Part268 (cell12399)

noncomputable def sourceNumerics12399 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12399 (cell12399 i)
      scalarRow12399.M scalarRow12399.H scalarRow12399.xi := by
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
    energy_allowance := scalarRow12399.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12399]
    centre_nonneg := (scalarRow12399.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12399])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12399