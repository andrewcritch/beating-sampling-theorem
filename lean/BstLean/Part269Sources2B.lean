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
import BstLean.Part269Direction2
import BstLean.Part269Shared2
import BstLean.Part269Finite
import BstLean.Part269Rows2
import BstLean.Part269Source
/-! Actual 12413 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12413
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12413 ≤ (1.036224488420 : ℝ) := by
  have hr : (111.413643688733 : ℝ) ≤ √(12413 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.413643688733 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12413 12413 (11 / 1000) ≤
    (0.008579623486 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12413) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.413643688733 : ℝ) ≤ √(12413 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12413)
  have hdiv : K / √(12413 : ℝ) ≤ K / 111.413643688733 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.413643688733 ≤ (0.008579623486 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12413.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12413 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12413 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12413 := gPlus_lower 12413
end BstLean.Part269.N12413

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12413
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036224488419 : ℝ) ≤ wn 12413 := by
  have hn : √(12413 : ℝ) ≤ 111.413643688734 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12413 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.413643688734 ≤ 2 / √(12413 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257807903 : ℝ) ≤ rhoBar 12413 BstLean.Part154.csC ∧
    rhoBar 12413 BstLean.Part154.csC ≤ 0.000257808303 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036224488419 : ℝ) / (1.295212 * 12413) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036224488420 : ℝ) / (1.29521 * 12413) := by gcongr
      _ ≤ (0.000257808303 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12413 BstLean.Part154.csC) ≤ 0.001031299678 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12413 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12413 BstLean.Part154.csC) (piBar (rhoBar 12413 BstLean.Part154.csC)) ≤ 0.000196915937 ∧
    cc1 (rhoBar 12413 BstLean.Part154.csC) (piBar (rhoBar 12413 BstLean.Part154.csC)) ≤ 0.000125298874 ∧
    cc2 (rhoBar 12413 BstLean.Part154.csC) ≤ 0.000072736902 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12413 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12413 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12413 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12413 BstLean.Part154.csC * nuR (rhoBar 12413 BstLean.Part154.csC)) ≤ 0.000515633223 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257808303 : ℝ) * 0.001031299678 := by gcongr
      _ ≤ (0.000515633223 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12413 BstLean.Part154.csC) * nuR (rhoBar 12413 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001031299678 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12413 BstLean.Part154.csC) * rhoBar 12413 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257808303 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257808303 / 2 + 0.399 * 0.001031299678 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196915937 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515633223 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125298874 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257808303 / 1.414213562 := by gcongr
      _ ≤ (0.000072736902 : ℝ) := by norm_num

end BstLean.Part269.N12413

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12413
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12413 BstLean.Part154.csC) (piBar (rhoBar 12413 BstLean.Part154.csC)) ≤ 1.67454E-7 := by
  have hr0 : 0 ≤ rhoBar 12413 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12413 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12413 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12413 BstLean.Part154.csC) (piBar (rhoBar 12413 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12413 BstLean.Part154.csC) (piBar (rhoBar 12413 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12413 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196915937 : ℝ) ^ 2 + 0.000125298874 ^ 2 + 3 * 0.000072736902 ^ 2 +
        2 * 0.797885 * 0.000196915937 * 0.000125298874 + 2 * 0.000196915937 * 0.000072736902 +
        4 * 0.797885 * 0.000125298874 * 0.000072736902 := by gcongr
    _ ≤ (1.67454E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12413 BstLean.Part154.csC Θ ≤ 0.002692236095 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12413 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12413 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12413 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12413 BstLean.Part154.csC) (piBar (rhoBar 12413 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12413 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036224488420 * 1.67454E-7 / (0.000257807903 : ℝ) := by gcongr
    _ ≤ 0.002692236095 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12413 BstLean.Part154.csC Θ ≤ 0.002988385339 + 0.000680285096 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12413 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12413 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12413 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036224488420 : ℝ) * ((2 * Θ * 0.000257808303 +
        (6863 / 10000) * 0.000257808303 * 12413 * 0.001031299678) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002988385339 + 0.000680285096 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12413 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12413 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12413 0.011 Θ ∧ gammaRatio 12413 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12413 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036224488420 : ℝ) * 0.525 / ((1 - 0.011) * 12413) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12413 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12413 0.011 Θ) :=
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
    badAllowance 12413 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12413 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12413 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12413 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12413 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12413 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12413 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12413 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12413 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12413 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12413 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036224488420 : ℝ) * 12413 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12413 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004088385339 + 0.003372521191 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12413

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12413
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12413 BstLean.Part154.csC) (piBar (rhoBar 12413 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12413 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12413 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12413 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12413 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12413 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12413 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12413 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12413 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12413 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12413 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12413 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12413 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12413 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12413 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053094205281 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12413) ≤ 0.010718952738 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12413 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036224488420)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010718952738 + 2 * 0.737676 / 12413) := by gcongr
    _ ≤ (0.053094205281 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12413 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12413

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12413
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490289212 : ℝ) ≤ plow 12413 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12413) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053365558965)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413423950) : eMP 12413 0.011 xi bn ≤ 0.001216487574 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12413 : ℝ) * (1 - 0.011))) ≤ 0.000601415560 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001413423950 / (12413 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601415560 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601415560 : ℝ) + 3.141593 * 0.053365558965 / (12413 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001216487574 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053365558965)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413423950) : PiBarMP 12413 12 0.011 xi bn ≤ 0.163125599529 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12413 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037595530985 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.799174184648 : ℝ) ≤ √((12413 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.413643688733 : ℝ) ≤ √(12413 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12413) ≤ 0.125051185847 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037595530985 + 0.053365558965 * 1.772454 / (2 * (110.799174184648 : ℝ))) * (1 + 0.001216487574) +
        8 / (12413 * 111.413643688733) + 0.125051185847 := by gcongr
    _ ≤ (0.163125599529 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053365558965)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413423950) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284104072960) :
    parallelOracle 12413 0.011 xi bn cd ≤ 0.164142952375 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12413 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12413 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490289212 : ℝ) ≤ plow 12413 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.413643688733 : ℝ) ≤ √(12413 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284104072960 : ℝ) / (2 * 0.560490289212 * 111.413643688733)) * 0.163125599529 +
        0.284104072960 ^ 2 / (2 * 0.560490289212 * 111.413643688733) := by gcongr
    _ ≤ (0.164142952375 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053365558965) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413423950)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284104072960) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12413 12413 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490289212 : ℝ) ≤ plow 12413 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.413643688733 : ℝ) ≤ √(12413 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12413 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12413 Θ 1.22 ≤ 0.011902496464 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.413643688733 := by gcongr <;> linarith
      _ ≤ (0.011902496464 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12413 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12413 12413 0.011 ≤ 0.008579623486 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12413 12413 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12413 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12413 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12413 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12413 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164142952375 + 0.011902496464 + (0.008579623486 : ℝ) *
        (1 + 2 * (0.284104072960 + 0.011902496464) / (0.560490289212 * 111.413643688733))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12413]

end BstLean.Part269.N12413

/-! The original eight local profiles supply actual 12413 moment certificates. -/
namespace BstLean.Part269.N12413
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12413 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12413 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12413 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053365558965 ∧
    0 ≤ bN 12413 BstLean.Part154.csC (groupTheta g) ∧ bN 12413 BstLean.Part154.csC (groupTheta g) ≤ 0.001413423950 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12413 12413 0.011
      (momentAllowance 12413 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12413 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12413 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12413 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12413 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12413 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231009867679 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12413 0.011
      (momentAllowance 12413 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12413 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12413
/-! The actual computed-centre upper energy formula at 12413. -/
namespace BstLean.Part269.N12413
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12413

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12413
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12413)
open BstLean.Part268 (cell12413)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086376633469
  | 2 => 0.087336843433
  | 3 => 0.088297924815
  | 4 => 0.089261910412
  | 5 => 0.090231236170
  | 6 => 0.091208798011
  | 7 => 0.092198013465
  | 8 => 0.093202888049
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12413 12413 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12413 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12413

/-! Actual upper energy certificates on all 43 source endpoints at 12413. -/
namespace BstLean.Part269.N12413
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12413)
open BstLean.Part268 (cell12413)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12413 (gMinus 12413) (1 - (cell12413 i).lower) ≤ 1 ∧
    energyUpper 12413 (gMinus 12413) (BstLean.Part211.gPlus 12413)
      (finiteEnergy 12413 12413 0.011) (1 - (cell12413 i).lower) ≤
      (cell12413 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨10,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨11,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨12,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨13,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨14,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨15,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨16,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨17,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨18,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨19,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨20,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨21,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨22,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨23,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨24,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨25,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨26,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨27,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨28,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨29,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨30,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨31,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨32,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨33,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨34,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨35,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨36,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨37,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨38,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨39,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨40,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨41,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨42,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨43,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨44,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨45,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨46,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨47,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨48,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨49,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨50,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨51,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12413) (by norm_num)
        (q := 1 - (cell12413 ⟨52,by decide⟩).lower)
        (by norm_num [cell12413]) (by norm_num [cell12413])
      exact ⟨E.1,E.2.trans (by norm_num [cell12413])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12413

/-! Source-cell containment and simple scalar guards at 12413. -/
namespace BstLean.Part269.N12413
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12413)
open BstLean.Part268 (cell12413)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12413 ⟨10,by decide⟩).lower ∧ (cell12413 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12413 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12413 ⟨11,by decide⟩).lower ∧ (cell12413 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12413 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12413 ⟨12,by decide⟩).lower ∧ (cell12413 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12413 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12413 ⟨13,by decide⟩).lower ∧ (cell12413 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12413 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12413 ⟨14,by decide⟩).lower ∧ (cell12413 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12413 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12413 ⟨15,by decide⟩).lower ∧ (cell12413 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12413 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12413 ⟨16,by decide⟩).lower ∧ (cell12413 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12413 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12413 ⟨17,by decide⟩).lower ∧ (cell12413 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12413 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12413 ⟨18,by decide⟩).lower ∧ (cell12413 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12413 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12413 ⟨19,by decide⟩).lower ∧ (cell12413 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12413 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12413 ⟨20,by decide⟩).lower ∧ (cell12413 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12413 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12413 ⟨21,by decide⟩).lower ∧ (cell12413 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12413 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12413 ⟨22,by decide⟩).lower ∧ (cell12413 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12413 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12413 ⟨23,by decide⟩).lower ∧ (cell12413 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12413 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12413 ⟨24,by decide⟩).lower ∧ (cell12413 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12413 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12413 ⟨25,by decide⟩).lower ∧ (cell12413 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12413 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12413 ⟨26,by decide⟩).lower ∧ (cell12413 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12413 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12413 ⟨27,by decide⟩).lower ∧ (cell12413 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12413 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12413 ⟨28,by decide⟩).lower ∧ (cell12413 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12413 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12413 ⟨29,by decide⟩).lower ∧ (cell12413 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12413 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12413 ⟨30,by decide⟩).lower ∧ (cell12413 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12413 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12413 ⟨31,by decide⟩).lower ∧ (cell12413 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12413 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12413 ⟨32,by decide⟩).lower ∧ (cell12413 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12413 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12413 ⟨33,by decide⟩).lower ∧ (cell12413 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12413 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12413 ⟨34,by decide⟩).lower ∧ (cell12413 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12413 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12413 ⟨35,by decide⟩).lower ∧ (cell12413 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12413 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12413 ⟨36,by decide⟩).lower ∧ (cell12413 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12413 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12413 ⟨37,by decide⟩).lower ∧ (cell12413 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12413 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12413 ⟨38,by decide⟩).lower ∧ (cell12413 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12413 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12413 ⟨39,by decide⟩).lower ∧ (cell12413 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12413 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12413 ⟨40,by decide⟩).lower ∧ (cell12413 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12413 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12413 ⟨41,by decide⟩).lower ∧ (cell12413 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12413 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12413 ⟨42,by decide⟩).lower ∧ (cell12413 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12413 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12413 ⟨43,by decide⟩).lower ∧ (cell12413 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12413 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12413 ⟨44,by decide⟩).lower ∧ (cell12413 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12413 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12413 ⟨45,by decide⟩).lower ∧ (cell12413 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12413 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12413 ⟨46,by decide⟩).lower ∧ (cell12413 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12413 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12413 ⟨47,by decide⟩).lower ∧ (cell12413 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12413 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12413 ⟨48,by decide⟩).lower ∧ (cell12413 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12413 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12413 ⟨49,by decide⟩).lower ∧ (cell12413 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12413 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12413 ⟨50,by decide⟩).lower ∧ (cell12413 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12413 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12413 ⟨51,by decide⟩).lower ∧ (cell12413 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12413 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12413 ⟨52,by decide⟩).lower ∧ (cell12413 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12413 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12413 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12413 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12413,cell12413,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12413 i).lower ∧
    (cell12413 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12413 i).upper ≤ (0.532 : ℝ) ∧
    (cell12413 i).centre ≤ (0.1 : ℝ) ∧ (cell12413 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12413 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12413 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12413

/-! The local source numeric instances at 12413 have no network premises. -/
namespace BstLean.Part269.N12413
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12413)
open BstLean.Part268 (cell12413)

noncomputable def sourceNumerics12413 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12413 (cell12413 i)
      scalarRow12413.M scalarRow12413.H scalarRow12413.xi := by
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
    energy_allowance := scalarRow12413.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12413]
    centre_nonneg := (scalarRow12413.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12413])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12413
/-! Actual 12414 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12414
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12414 ≤ (1.036223016395 : ℝ) := by
  have hr : (111.418131379053 : ℝ) ≤ √(12414 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.418131379053 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12414 12414 (11 / 1000) ≤
    (0.008579277914 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12414) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.418131379053 : ℝ) ≤ √(12414 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12414)
  have hdiv : K / √(12414 : ℝ) ≤ K / 111.418131379053 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.418131379053 ≤ (0.008579277914 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12414.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12414 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12414 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12414 := gPlus_lower 12414
end BstLean.Part269.N12414

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12414
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036223016394 : ℝ) ≤ wn 12414 := by
  have hn : √(12414 : ℝ) ≤ 111.418131379054 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12414 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.418131379054 ≤ 2 / √(12414 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257786770 : ℝ) ≤ rhoBar 12414 BstLean.Part154.csC ∧
    rhoBar 12414 BstLean.Part154.csC ≤ 0.000257787169 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036223016394 : ℝ) / (1.295212 * 12414) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036223016395 : ℝ) / (1.29521 * 12414) := by gcongr
      _ ≤ (0.000257787169 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12414 BstLean.Part154.csC) ≤ 0.001031215131 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12414 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12414 BstLean.Part154.csC) (piBar (rhoBar 12414 BstLean.Part154.csC)) ≤ 0.000196899794 ∧
    cc1 (rhoBar 12414 BstLean.Part154.csC) (piBar (rhoBar 12414 BstLean.Part154.csC)) ≤ 0.000125288602 ∧
    cc2 (rhoBar 12414 BstLean.Part154.csC) ≤ 0.000072730940 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12414 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12414 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12414 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12414 BstLean.Part154.csC * nuR (rhoBar 12414 BstLean.Part154.csC)) ≤ 0.000515590952 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257787169 : ℝ) * 0.001031215131 := by gcongr
      _ ≤ (0.000515590952 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12414 BstLean.Part154.csC) * nuR (rhoBar 12414 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001031215131 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12414 BstLean.Part154.csC) * rhoBar 12414 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257787169 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257787169 / 2 + 0.399 * 0.001031215131 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196899794 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515590952 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125288602 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257787169 / 1.414213562 := by gcongr
      _ ≤ (0.000072730940 : ℝ) := by norm_num

end BstLean.Part269.N12414

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12414
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12414 BstLean.Part154.csC) (piBar (rhoBar 12414 BstLean.Part154.csC)) ≤ 1.67427E-7 := by
  have hr0 : 0 ≤ rhoBar 12414 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12414 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12414 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12414 BstLean.Part154.csC) (piBar (rhoBar 12414 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12414 BstLean.Part154.csC) (piBar (rhoBar 12414 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12414 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196899794 : ℝ) ^ 2 + 0.000125288602 ^ 2 + 3 * 0.000072730940 ^ 2 +
        2 * 0.797885 * 0.000196899794 * 0.000125288602 + 2 * 0.000196899794 * 0.000072730940 +
        4 * 0.797885 * 0.000125288602 * 0.000072730940 := by gcongr
    _ ≤ (1.67427E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12414 BstLean.Part154.csC Θ ≤ 0.002692018850 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12414 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12414 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12414 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12414 BstLean.Part154.csC) (piBar (rhoBar 12414 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12414 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036223016395 * 1.67427E-7 / (0.000257786770 : ℝ) := by gcongr
    _ ≤ 0.002692018850 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12414 BstLean.Part154.csC Θ ≤ 0.002988131856 + 0.000680228363 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12414 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12414 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12414 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036223016395 : ℝ) * ((2 * Θ * 0.000257787169 +
        (6863 / 10000) * 0.000257787169 * 12414 * 0.001031215131) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002988131856 + 0.000680228363 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12414 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12414 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12414 0.011 Θ ∧ gammaRatio 12414 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12414 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036223016395 : ℝ) * 0.525 / ((1 - 0.011) * 12414) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12414 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12414 0.011 Θ) :=
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
    badAllowance 12414 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12414 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12414 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12414 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12414 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12414 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12414 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12414 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12414 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12414 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12414 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036223016395 : ℝ) * 12414 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12414 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004088131856 + 0.003372247213 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12414

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12414
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12414 BstLean.Part154.csC) (piBar (rhoBar 12414 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12414 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12414 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12414 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12414 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12414 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12414 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12414 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12414 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12414 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12414 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12414 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12414 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12414 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12414 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053092043306 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12414) ≤ 0.010718521001 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12414 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036223016395)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010718521001 + 2 * 0.737676 / 12414) := by gcongr
    _ ≤ (0.053092043306 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12414 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12414

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12414
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490336547 : ℝ) ≤ plow 12414 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12414) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053365161643)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413309897) : eMP 12414 0.011 xi bn ≤ 0.001216389396 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12414 : ℝ) * (1 - 0.011))) ≤ 0.000601367072 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001413309897 / (12414 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601367072 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601367072 : ℝ) + 3.141593 * 0.053365161643 / (12414 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001216389396 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053365161643)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413309897) : PiBarMP 12414 12 0.011 xi bn ≤ 0.163119019183 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12414 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037594014112 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.803637124419 : ℝ) ≤ √((12414 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.418131379053 : ℝ) ≤ √(12414 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12414) ≤ 0.125046149046 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037594014112 + 0.053365161643 * 1.772454 / (2 * (110.803637124419 : ℝ))) * (1 + 0.001216389396) +
        8 / (12414 * 111.418131379053) + 0.125046149046 := by gcongr
    _ ≤ (0.163119019183 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053365161643)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413309897) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284101051016) :
    parallelOracle 12414 0.011 xi bn cd ≤ 0.164136298303 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12414 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12414 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490336547 : ℝ) ≤ plow 12414 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.418131379053 : ℝ) ≤ √(12414 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284101051016 : ℝ) / (2 * 0.560490336547 * 111.418131379053)) * 0.163119019183 +
        0.284101051016 ^ 2 / (2 * 0.560490336547 * 111.418131379053) := by gcongr
    _ ≤ (0.164136298303 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053365161643) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413309897)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284101051016) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12414 12414 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490336547 : ℝ) ≤ plow 12414 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.418131379053 : ℝ) ≤ √(12414 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12414 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12414 Θ 1.22 ≤ 0.011902017056 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.418131379053 := by gcongr <;> linarith
      _ ≤ (0.011902017056 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12414 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12414 12414 0.011 ≤ 0.008579277914 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12414 12414 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12414 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12414 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12414 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12414 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164136298303 + 0.011902017056 + (0.008579277914 : ℝ) *
        (1 + 2 * (0.284101051016 + 0.011902017056) / (0.560490336547 * 111.418131379053))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12414]

end BstLean.Part269.N12414

/-! The original eight local profiles supply actual 12414 moment certificates. -/
namespace BstLean.Part269.N12414
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12414 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12414 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12414 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053365161643 ∧
    0 ≤ bN 12414 BstLean.Part154.csC (groupTheta g) ∧ bN 12414 BstLean.Part154.csC (groupTheta g) ≤ 0.001413309897 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12414 12414 0.011
      (momentAllowance 12414 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12414 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12414 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12414 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12414 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12414 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231009007710 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12414 0.011
      (momentAllowance 12414 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12414 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12414
/-! The actual computed-centre upper energy formula at 12414. -/
namespace BstLean.Part269.N12414
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12414

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12414
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12414)
open BstLean.Part268 (cell12414)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086373355438
  | 2 => 0.087333496369
  | 3 => 0.088294497284
  | 4 => 0.089258388460
  | 5 => 0.090227602895
  | 6 => 0.091205033091
  | 7 => 0.092194092631
  | 8 => 0.093198782506
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12414 12414 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12414 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12414

/-! Actual upper energy certificates on all 43 source endpoints at 12414. -/
namespace BstLean.Part269.N12414
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12414)
open BstLean.Part268 (cell12414)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12414 (gMinus 12414) (1 - (cell12414 i).lower) ≤ 1 ∧
    energyUpper 12414 (gMinus 12414) (BstLean.Part211.gPlus 12414)
      (finiteEnergy 12414 12414 0.011) (1 - (cell12414 i).lower) ≤
      (cell12414 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨10,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨11,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨12,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨13,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨14,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨15,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨16,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨17,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨18,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨19,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨20,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨21,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨22,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨23,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨24,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨25,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨26,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨27,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨28,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨29,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨30,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨31,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨32,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨33,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨34,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨35,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨36,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨37,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨38,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨39,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨40,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨41,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨42,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨43,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨44,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨45,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨46,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨47,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨48,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨49,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨50,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨51,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12414) (by norm_num)
        (q := 1 - (cell12414 ⟨52,by decide⟩).lower)
        (by norm_num [cell12414]) (by norm_num [cell12414])
      exact ⟨E.1,E.2.trans (by norm_num [cell12414])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12414

/-! Source-cell containment and simple scalar guards at 12414. -/
namespace BstLean.Part269.N12414
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12414)
open BstLean.Part268 (cell12414)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12414 ⟨10,by decide⟩).lower ∧ (cell12414 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12414 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12414 ⟨11,by decide⟩).lower ∧ (cell12414 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12414 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12414 ⟨12,by decide⟩).lower ∧ (cell12414 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12414 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12414 ⟨13,by decide⟩).lower ∧ (cell12414 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12414 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12414 ⟨14,by decide⟩).lower ∧ (cell12414 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12414 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12414 ⟨15,by decide⟩).lower ∧ (cell12414 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12414 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12414 ⟨16,by decide⟩).lower ∧ (cell12414 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12414 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12414 ⟨17,by decide⟩).lower ∧ (cell12414 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12414 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12414 ⟨18,by decide⟩).lower ∧ (cell12414 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12414 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12414 ⟨19,by decide⟩).lower ∧ (cell12414 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12414 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12414 ⟨20,by decide⟩).lower ∧ (cell12414 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12414 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12414 ⟨21,by decide⟩).lower ∧ (cell12414 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12414 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12414 ⟨22,by decide⟩).lower ∧ (cell12414 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12414 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12414 ⟨23,by decide⟩).lower ∧ (cell12414 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12414 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12414 ⟨24,by decide⟩).lower ∧ (cell12414 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12414 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12414 ⟨25,by decide⟩).lower ∧ (cell12414 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12414 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12414 ⟨26,by decide⟩).lower ∧ (cell12414 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12414 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12414 ⟨27,by decide⟩).lower ∧ (cell12414 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12414 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12414 ⟨28,by decide⟩).lower ∧ (cell12414 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12414 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12414 ⟨29,by decide⟩).lower ∧ (cell12414 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12414 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12414 ⟨30,by decide⟩).lower ∧ (cell12414 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12414 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12414 ⟨31,by decide⟩).lower ∧ (cell12414 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12414 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12414 ⟨32,by decide⟩).lower ∧ (cell12414 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12414 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12414 ⟨33,by decide⟩).lower ∧ (cell12414 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12414 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12414 ⟨34,by decide⟩).lower ∧ (cell12414 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12414 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12414 ⟨35,by decide⟩).lower ∧ (cell12414 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12414 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12414 ⟨36,by decide⟩).lower ∧ (cell12414 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12414 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12414 ⟨37,by decide⟩).lower ∧ (cell12414 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12414 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12414 ⟨38,by decide⟩).lower ∧ (cell12414 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12414 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12414 ⟨39,by decide⟩).lower ∧ (cell12414 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12414 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12414 ⟨40,by decide⟩).lower ∧ (cell12414 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12414 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12414 ⟨41,by decide⟩).lower ∧ (cell12414 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12414 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12414 ⟨42,by decide⟩).lower ∧ (cell12414 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12414 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12414 ⟨43,by decide⟩).lower ∧ (cell12414 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12414 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12414 ⟨44,by decide⟩).lower ∧ (cell12414 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12414 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12414 ⟨45,by decide⟩).lower ∧ (cell12414 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12414 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12414 ⟨46,by decide⟩).lower ∧ (cell12414 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12414 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12414 ⟨47,by decide⟩).lower ∧ (cell12414 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12414 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12414 ⟨48,by decide⟩).lower ∧ (cell12414 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12414 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12414 ⟨49,by decide⟩).lower ∧ (cell12414 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12414 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12414 ⟨50,by decide⟩).lower ∧ (cell12414 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12414 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12414 ⟨51,by decide⟩).lower ∧ (cell12414 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12414 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12414 ⟨52,by decide⟩).lower ∧ (cell12414 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12414 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12414 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12414 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12414,cell12414,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12414 i).lower ∧
    (cell12414 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12414 i).upper ≤ (0.532 : ℝ) ∧
    (cell12414 i).centre ≤ (0.1 : ℝ) ∧ (cell12414 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12414 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12414 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12414

/-! The local source numeric instances at 12414 have no network premises. -/
namespace BstLean.Part269.N12414
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12414)
open BstLean.Part268 (cell12414)

noncomputable def sourceNumerics12414 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12414 (cell12414 i)
      scalarRow12414.M scalarRow12414.H scalarRow12414.xi := by
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
    energy_allowance := scalarRow12414.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12414]
    centre_nonneg := (scalarRow12414.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12414])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12414
/-! Actual 12415 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12415
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12415 ≤ (1.036221544548 : ℝ) := by
  have hr : (111.422618888626 : ℝ) ≤ √(12415 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.422618888626 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12415 12415 (11 / 1000) ≤
    (0.008578932384 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12415) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.422618888626 : ℝ) ≤ √(12415 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12415)
  have hdiv : K / √(12415 : ℝ) ≤ K / 111.422618888626 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.422618888626 ≤ (0.008578932384 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12415.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12415 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12415 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12415 := gPlus_lower 12415
end BstLean.Part269.N12415

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12415
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036221544547 : ℝ) ≤ wn 12415 := by
  have hn : √(12415 : ℝ) ≤ 111.422618888627 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12415 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.422618888627 ≤ 2 / √(12415 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257765639 : ℝ) ≤ rhoBar 12415 BstLean.Part154.csC ∧
    rhoBar 12415 BstLean.Part154.csC ≤ 0.000257766038 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036221544547 : ℝ) / (1.295212 * 12415) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036221544548 : ℝ) / (1.29521 * 12415) := by gcongr
      _ ≤ (0.000257766038 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12415 BstLean.Part154.csC) ≤ 0.001031130596 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12415 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12415 BstLean.Part154.csC) (piBar (rhoBar 12415 BstLean.Part154.csC)) ≤ 0.000196883653 ∧
    cc1 (rhoBar 12415 BstLean.Part154.csC) (piBar (rhoBar 12415 BstLean.Part154.csC)) ≤ 0.000125278331 ∧
    cc2 (rhoBar 12415 BstLean.Part154.csC) ≤ 0.000072724978 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12415 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12415 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12415 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12415 BstLean.Part154.csC * nuR (rhoBar 12415 BstLean.Part154.csC)) ≤ 0.000515548687 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257766038 : ℝ) * 0.001031130596 := by gcongr
      _ ≤ (0.000515548687 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12415 BstLean.Part154.csC) * nuR (rhoBar 12415 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001031130596 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12415 BstLean.Part154.csC) * rhoBar 12415 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257766038 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257766038 / 2 + 0.399 * 0.001031130596 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196883653 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515548687 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125278331 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257766038 / 1.414213562 := by gcongr
      _ ≤ (0.000072724978 : ℝ) := by norm_num

end BstLean.Part269.N12415

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12415
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12415 BstLean.Part154.csC) (piBar (rhoBar 12415 BstLean.Part154.csC)) ≤ 1.67400E-7 := by
  have hr0 : 0 ≤ rhoBar 12415 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12415 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12415 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12415 BstLean.Part154.csC) (piBar (rhoBar 12415 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12415 BstLean.Part154.csC) (piBar (rhoBar 12415 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12415 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196883653 : ℝ) ^ 2 + 0.000125278331 ^ 2 + 3 * 0.000072724978 ^ 2 +
        2 * 0.797885 * 0.000196883653 * 0.000125278331 + 2 * 0.000196883653 * 0.000072724978 +
        4 * 0.797885 * 0.000125278331 * 0.000072724978 := by gcongr
    _ ≤ (1.67400E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12415 BstLean.Part154.csC Θ ≤ 0.002691801549 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12415 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12415 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12415 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12415 BstLean.Part154.csC) (piBar (rhoBar 12415 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12415 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036221544548 * 1.67400E-7 / (0.000257765639 : ℝ) := by gcongr
    _ ≤ 0.002691801549 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12415 BstLean.Part154.csC Θ ≤ 0.002987878404 + 0.000680171638 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12415 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12415 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12415 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036221544548 : ℝ) * ((2 * Θ * 0.000257766038 +
        (6863 / 10000) * 0.000257766038 * 12415 * 0.001031130596) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002987878404 + 0.000680171638 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12415 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12415 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12415 0.011 Θ ∧ gammaRatio 12415 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12415 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036221544548 : ℝ) * 0.525 / ((1 - 0.011) * 12415) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12415 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12415 0.011 Θ) :=
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
    badAllowance 12415 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12415 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12415 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12415 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12415 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12415 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12415 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12415 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12415 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12415 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12415 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036221544548 : ℝ) * 12415 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12415 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004087878404 + 0.003371973187 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12415

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12415
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12415 BstLean.Part154.csC) (piBar (rhoBar 12415 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12415 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12415 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12415 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12415 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12415 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12415 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12415 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12415 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12415 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12415 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12415 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12415 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12415 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12415 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053089881593 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12415) ≤ 0.010718089316 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12415 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036221544548)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010718089316 + 2 * 0.737676 / 12415) := by gcongr
    _ ≤ (0.053089881593 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12415 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12415

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12415
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490383874 : ℝ) ≤ plow 12415 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12415) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053364764328)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413195814) : eMP 12415 0.011 xi bn ≤ 0.001216291213 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12415 : ℝ) * (1 - 0.011))) ≤ 0.000601318581 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001413195814 / (12415 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601318581 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601318581 : ℝ) + 3.141593 * 0.053364764328 / (12415 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001216291213 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053364764328)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413195814) : PiBarMP 12415 12 0.011 xi bn ≤ 0.163112438986 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12415 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037592496778 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.808099884439 : ℝ) ≤ √((12415 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.422618888626 : ℝ) ≤ √(12415 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12415) ≤ 0.125041112853 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037592496778 + 0.053364764328 * 1.772454 / (2 * (110.808099884439 : ℝ))) * (1 + 0.001216291213) +
        8 / (12415 * 111.422618888626) + 0.125041112853 := by gcongr
    _ ≤ (0.163112438986 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053364764328)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413195814) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284098029346) :
    parallelOracle 12415 0.011 xi bn cd ≤ 0.164129644390 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12415 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12415 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490383874 : ℝ) ≤ plow 12415 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.422618888626 : ℝ) ≤ √(12415 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284098029346 : ℝ) / (2 * 0.560490383874 * 111.422618888626)) * 0.163112438986 +
        0.284098029346 ^ 2 / (2 * 0.560490383874 * 111.422618888626) := by gcongr
    _ ≤ (0.164129644390 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053364764328) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413195814)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284098029346) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12415 12415 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490383874 : ℝ) ≤ plow 12415 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.422618888626 : ℝ) ≤ √(12415 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12415 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12415 Θ 1.22 ≤ 0.011901537706 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.422618888626 := by gcongr <;> linarith
      _ ≤ (0.011901537706 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12415 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12415 12415 0.011 ≤ 0.008578932384 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12415 12415 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12415 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12415 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12415 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12415 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164129644390 + 0.011901537706 + (0.008578932384 : ℝ) *
        (1 + 2 * (0.284098029346 + 0.011901537706) / (0.560490383874 * 111.422618888626))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12415]

end BstLean.Part269.N12415

/-! The original eight local profiles supply actual 12415 moment certificates. -/
namespace BstLean.Part269.N12415
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12415 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12415 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12415 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053364764328 ∧
    0 ≤ bN 12415 BstLean.Part154.csC (groupTheta g) ∧ bN 12415 BstLean.Part154.csC (groupTheta g) ≤ 0.001413195814 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12415 12415 0.011
      (momentAllowance 12415 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12415 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12415 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12415 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12415 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12415 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231008147753 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12415 0.011
      (momentAllowance 12415 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12415 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12415
/-! The actual computed-centre upper energy formula at 12415. -/
namespace BstLean.Part269.N12415
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12415

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12415
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12415)
open BstLean.Part268 (cell12415)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086370078870
  | 2 => 0.087330150833
  | 3 => 0.088291071362
  | 4 => 0.089254868214
  | 5 => 0.090223971445
  | 6 => 0.091201270140
  | 7 => 0.092190173940
  | 8 => 0.093194679315
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12415 12415 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12415 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12415

/-! Actual upper energy certificates on all 43 source endpoints at 12415. -/
namespace BstLean.Part269.N12415
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12415)
open BstLean.Part268 (cell12415)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12415 (gMinus 12415) (1 - (cell12415 i).lower) ≤ 1 ∧
    energyUpper 12415 (gMinus 12415) (BstLean.Part211.gPlus 12415)
      (finiteEnergy 12415 12415 0.011) (1 - (cell12415 i).lower) ≤
      (cell12415 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨10,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨11,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨12,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨13,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨14,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨15,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨16,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨17,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨18,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨19,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨20,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨21,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨22,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨23,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨24,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨25,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨26,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨27,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨28,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨29,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨30,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨31,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨32,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨33,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨34,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨35,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨36,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨37,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨38,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨39,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨40,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨41,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨42,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨43,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨44,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨45,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨46,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨47,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨48,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨49,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨50,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨51,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12415) (by norm_num)
        (q := 1 - (cell12415 ⟨52,by decide⟩).lower)
        (by norm_num [cell12415]) (by norm_num [cell12415])
      exact ⟨E.1,E.2.trans (by norm_num [cell12415])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12415

/-! Source-cell containment and simple scalar guards at 12415. -/
namespace BstLean.Part269.N12415
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12415)
open BstLean.Part268 (cell12415)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12415 ⟨10,by decide⟩).lower ∧ (cell12415 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12415 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12415 ⟨11,by decide⟩).lower ∧ (cell12415 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12415 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12415 ⟨12,by decide⟩).lower ∧ (cell12415 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12415 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12415 ⟨13,by decide⟩).lower ∧ (cell12415 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12415 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12415 ⟨14,by decide⟩).lower ∧ (cell12415 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12415 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12415 ⟨15,by decide⟩).lower ∧ (cell12415 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12415 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12415 ⟨16,by decide⟩).lower ∧ (cell12415 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12415 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12415 ⟨17,by decide⟩).lower ∧ (cell12415 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12415 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12415 ⟨18,by decide⟩).lower ∧ (cell12415 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12415 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12415 ⟨19,by decide⟩).lower ∧ (cell12415 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12415 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12415 ⟨20,by decide⟩).lower ∧ (cell12415 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12415 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12415 ⟨21,by decide⟩).lower ∧ (cell12415 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12415 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12415 ⟨22,by decide⟩).lower ∧ (cell12415 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12415 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12415 ⟨23,by decide⟩).lower ∧ (cell12415 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12415 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12415 ⟨24,by decide⟩).lower ∧ (cell12415 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12415 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12415 ⟨25,by decide⟩).lower ∧ (cell12415 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12415 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12415 ⟨26,by decide⟩).lower ∧ (cell12415 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12415 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12415 ⟨27,by decide⟩).lower ∧ (cell12415 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12415 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12415 ⟨28,by decide⟩).lower ∧ (cell12415 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12415 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12415 ⟨29,by decide⟩).lower ∧ (cell12415 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12415 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12415 ⟨30,by decide⟩).lower ∧ (cell12415 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12415 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12415 ⟨31,by decide⟩).lower ∧ (cell12415 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12415 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12415 ⟨32,by decide⟩).lower ∧ (cell12415 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12415 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12415 ⟨33,by decide⟩).lower ∧ (cell12415 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12415 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12415 ⟨34,by decide⟩).lower ∧ (cell12415 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12415 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12415 ⟨35,by decide⟩).lower ∧ (cell12415 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12415 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12415 ⟨36,by decide⟩).lower ∧ (cell12415 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12415 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12415 ⟨37,by decide⟩).lower ∧ (cell12415 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12415 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12415 ⟨38,by decide⟩).lower ∧ (cell12415 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12415 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12415 ⟨39,by decide⟩).lower ∧ (cell12415 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12415 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12415 ⟨40,by decide⟩).lower ∧ (cell12415 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12415 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12415 ⟨41,by decide⟩).lower ∧ (cell12415 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12415 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12415 ⟨42,by decide⟩).lower ∧ (cell12415 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12415 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12415 ⟨43,by decide⟩).lower ∧ (cell12415 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12415 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12415 ⟨44,by decide⟩).lower ∧ (cell12415 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12415 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12415 ⟨45,by decide⟩).lower ∧ (cell12415 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12415 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12415 ⟨46,by decide⟩).lower ∧ (cell12415 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12415 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12415 ⟨47,by decide⟩).lower ∧ (cell12415 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12415 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12415 ⟨48,by decide⟩).lower ∧ (cell12415 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12415 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12415 ⟨49,by decide⟩).lower ∧ (cell12415 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12415 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12415 ⟨50,by decide⟩).lower ∧ (cell12415 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12415 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12415 ⟨51,by decide⟩).lower ∧ (cell12415 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12415 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12415 ⟨52,by decide⟩).lower ∧ (cell12415 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12415 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12415 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12415 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12415,cell12415,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12415 i).lower ∧
    (cell12415 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12415 i).upper ≤ (0.532 : ℝ) ∧
    (cell12415 i).centre ≤ (0.1 : ℝ) ∧ (cell12415 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12415 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12415 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12415

/-! The local source numeric instances at 12415 have no network premises. -/
namespace BstLean.Part269.N12415
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12415)
open BstLean.Part268 (cell12415)

noncomputable def sourceNumerics12415 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12415 (cell12415 i)
      scalarRow12415.M scalarRow12415.H scalarRow12415.xi := by
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
    energy_allowance := scalarRow12415.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12415]
    centre_nonneg := (scalarRow12415.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12415])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12415
/-! Actual 12416 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12416
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12416 ≤ (1.036220072880 : ℝ) := by
  have hr : (111.427106217472 : ℝ) ≤ √(12416 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.427106217472 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12416 12416 (11 / 1000) ≤
    (0.008578586895 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12416) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.427106217472 : ℝ) ≤ √(12416 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12416)
  have hdiv : K / √(12416 : ℝ) ≤ K / 111.427106217472 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.427106217472 ≤ (0.008578586895 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12416.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12416 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12416 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12416 := gPlus_lower 12416
end BstLean.Part269.N12416

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12416
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036220072879 : ℝ) ≤ wn 12416 := by
  have hn : √(12416 : ℝ) ≤ 111.427106217473 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12416 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.427106217473 ≤ 2 / √(12416 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257744513 : ℝ) ≤ rhoBar 12416 BstLean.Part154.csC ∧
    rhoBar 12416 BstLean.Part154.csC ≤ 0.000257744912 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036220072879 : ℝ) / (1.295212 * 12416) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036220072880 : ℝ) / (1.29521 * 12416) := by gcongr
      _ ≤ (0.000257744912 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12416 BstLean.Part154.csC) ≤ 0.001031046081 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12416 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12416 BstLean.Part154.csC) (piBar (rhoBar 12416 BstLean.Part154.csC)) ≤ 0.000196867516 ∧
    cc1 (rhoBar 12416 BstLean.Part154.csC) (piBar (rhoBar 12416 BstLean.Part154.csC)) ≤ 0.000125268063 ∧
    cc2 (rhoBar 12416 BstLean.Part154.csC) ≤ 0.000072719017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12416 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12416 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12416 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12416 BstLean.Part154.csC * nuR (rhoBar 12416 BstLean.Part154.csC)) ≤ 0.000515506432 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257744912 : ℝ) * 0.001031046081 := by gcongr
      _ ≤ (0.000515506432 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12416 BstLean.Part154.csC) * nuR (rhoBar 12416 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001031046081 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12416 BstLean.Part154.csC) * rhoBar 12416 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257744912 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257744912 / 2 + 0.399 * 0.001031046081 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196867516 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515506432 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125268063 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257744912 / 1.414213562 := by gcongr
      _ ≤ (0.000072719017 : ℝ) := by norm_num

end BstLean.Part269.N12416

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12416
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12416 BstLean.Part154.csC) (piBar (rhoBar 12416 BstLean.Part154.csC)) ≤ 1.67372E-7 := by
  have hr0 : 0 ≤ rhoBar 12416 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12416 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12416 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12416 BstLean.Part154.csC) (piBar (rhoBar 12416 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12416 BstLean.Part154.csC) (piBar (rhoBar 12416 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12416 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196867516 : ℝ) ^ 2 + 0.000125268063 ^ 2 + 3 * 0.000072719017 ^ 2 +
        2 * 0.797885 * 0.000196867516 * 0.000125268063 + 2 * 0.000196867516 * 0.000072719017 +
        4 * 0.797885 * 0.000125268063 * 0.000072719017 := by gcongr
    _ ≤ (1.67372E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12416 BstLean.Part154.csC Θ ≤ 0.002691568081 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12416 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12416 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12416 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12416 BstLean.Part154.csC) (piBar (rhoBar 12416 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12416 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036220072880 * 1.67372E-7 / (0.000257744513 : ℝ) := by gcongr
    _ ≤ 0.002691568081 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12416 BstLean.Part154.csC Θ ≤ 0.002987625031 + 0.000680114927 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12416 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12416 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12416 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036220072880 : ℝ) * ((2 * Θ * 0.000257744912 +
        (6863 / 10000) * 0.000257744912 * 12416 * 0.001031046081) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002987625031 + 0.000680114927 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12416 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12416 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12416 0.011 Θ ∧ gammaRatio 12416 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12416 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036220072880 : ℝ) * 0.525 / ((1 - 0.011) * 12416) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12416 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12416 0.011 Θ) :=
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
    badAllowance 12416 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12416 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12416 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12416 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12416 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12416 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12416 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12416 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12416 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12416 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12416 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036220072880 : ℝ) * 12416 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12416 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004087625031 + 0.003371683008 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12416

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12416
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12416 BstLean.Part154.csC) (piBar (rhoBar 12416 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12416 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12416 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12416 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12416 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12416 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12416 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12416 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12416 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12416 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12416 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12416 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12416 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12416 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12416 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053087720147 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12416) ≤ 0.010717657684 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12416 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036220072880)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010717657684 + 2 * 0.737676 / 12416) := by gcongr
    _ ≤ (0.053087720147 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12416 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12416

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12416
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490431193 : ℝ) ≤ plow 12416 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12416) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053364358611)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413073243) : eMP 12416 0.011 xi bn ≤ 0.001216189425 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12416 : ℝ) * (1 - 0.011))) ≤ 0.000601268289 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001413073243 / (12416 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601268289 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601268289 : ℝ) + 3.141593 * 0.053364358611 / (12416 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001216189425 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053364358611)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413073243) : PiBarMP 12416 12 0.011 xi bn ≤ 0.163105746099 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12416 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037590866484 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.812562464731 : ℝ) ≤ √((12416 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.427106217472 : ℝ) ≤ √(12416 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12416) ≤ 0.125036077268 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037590866484 + 0.053364358611 * 1.772454 / (2 * (110.812562464731 : ℝ))) * (1 + 0.001216189425) +
        8 / (12416 * 111.427106217472) + 0.125036077268 := by gcongr
    _ ≤ (0.163105746099 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053364358611)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413073243) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284094989754) :
    parallelOracle 12416 0.011 xi bn cd ≤ 0.164122877434 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12416 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12416 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490431193 : ℝ) ≤ plow 12416 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.427106217472 : ℝ) ≤ √(12416 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284094989754 : ℝ) / (2 * 0.560490431193 * 111.427106217472)) * 0.163105746099 +
        0.284094989754 ^ 2 / (2 * 0.560490431193 * 111.427106217472) := by gcongr
    _ ≤ (0.164122877434 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053364358611) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001413073243)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284094989754) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12416 12416 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490431193 : ℝ) ≤ plow 12416 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.427106217472 : ℝ) ≤ √(12416 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12416 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12416 Θ 1.22 ≤ 0.011901058415 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.427106217472 := by gcongr <;> linarith
      _ ≤ (0.011901058415 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12416 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12416 12416 0.011 ≤ 0.008578586895 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12416 12416 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12416 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12416 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12416 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12416 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164122877434 + 0.011901058415 + (0.008578586895 : ℝ) *
        (1 + 2 * (0.284094989754 + 0.011901058415) / (0.560490431193 * 111.427106217472))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12416]

end BstLean.Part269.N12416

/-! The original eight local profiles supply actual 12416 moment certificates. -/
namespace BstLean.Part269.N12416
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12416 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12416 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12416 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053364358611 ∧
    0 ≤ bN 12416 BstLean.Part154.csC (groupTheta g) ∧ bN 12416 BstLean.Part154.csC (groupTheta g) ≤ 0.001413073243 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12416 12416 0.011
      (momentAllowance 12416 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12416 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12416 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12416 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12416 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12416 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231007269607 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12416 0.011
      (momentAllowance 12416 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12416 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12416
/-! The actual computed-centre upper energy formula at 12416. -/
namespace BstLean.Part269.N12416
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12416

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12416
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12416)
open BstLean.Part268 (cell12416)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086366803765
  | 2 => 0.087326806825
  | 3 => 0.088287647046
  | 4 => 0.089251349672
  | 5 => 0.090220341818
  | 6 => 0.091197509157
  | 7 => 0.092186257390
  | 8 => 0.093190578473
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12416 12416 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12416 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12416

/-! Actual upper energy certificates on all 43 source endpoints at 12416. -/
namespace BstLean.Part269.N12416
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12416)
open BstLean.Part268 (cell12416)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12416 (gMinus 12416) (1 - (cell12416 i).lower) ≤ 1 ∧
    energyUpper 12416 (gMinus 12416) (BstLean.Part211.gPlus 12416)
      (finiteEnergy 12416 12416 0.011) (1 - (cell12416 i).lower) ≤
      (cell12416 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨10,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨11,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨12,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨13,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨14,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨15,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨16,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨17,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨18,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨19,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨20,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨21,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨22,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨23,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨24,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨25,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨26,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨27,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨28,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨29,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨30,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨31,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨32,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨33,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨34,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨35,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨36,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨37,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨38,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨39,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨40,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨41,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨42,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨43,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨44,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨45,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨46,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨47,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨48,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨49,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨50,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨51,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12416) (by norm_num)
        (q := 1 - (cell12416 ⟨52,by decide⟩).lower)
        (by norm_num [cell12416]) (by norm_num [cell12416])
      exact ⟨E.1,E.2.trans (by norm_num [cell12416])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12416

/-! Source-cell containment and simple scalar guards at 12416. -/
namespace BstLean.Part269.N12416
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12416)
open BstLean.Part268 (cell12416)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12416 ⟨10,by decide⟩).lower ∧ (cell12416 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12416 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12416 ⟨11,by decide⟩).lower ∧ (cell12416 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12416 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12416 ⟨12,by decide⟩).lower ∧ (cell12416 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12416 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12416 ⟨13,by decide⟩).lower ∧ (cell12416 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12416 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12416 ⟨14,by decide⟩).lower ∧ (cell12416 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12416 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12416 ⟨15,by decide⟩).lower ∧ (cell12416 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12416 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12416 ⟨16,by decide⟩).lower ∧ (cell12416 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12416 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12416 ⟨17,by decide⟩).lower ∧ (cell12416 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12416 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12416 ⟨18,by decide⟩).lower ∧ (cell12416 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12416 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12416 ⟨19,by decide⟩).lower ∧ (cell12416 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12416 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12416 ⟨20,by decide⟩).lower ∧ (cell12416 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12416 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12416 ⟨21,by decide⟩).lower ∧ (cell12416 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12416 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12416 ⟨22,by decide⟩).lower ∧ (cell12416 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12416 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12416 ⟨23,by decide⟩).lower ∧ (cell12416 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12416 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12416 ⟨24,by decide⟩).lower ∧ (cell12416 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12416 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12416 ⟨25,by decide⟩).lower ∧ (cell12416 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12416 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12416 ⟨26,by decide⟩).lower ∧ (cell12416 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12416 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12416 ⟨27,by decide⟩).lower ∧ (cell12416 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12416 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12416 ⟨28,by decide⟩).lower ∧ (cell12416 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12416 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12416 ⟨29,by decide⟩).lower ∧ (cell12416 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12416 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12416 ⟨30,by decide⟩).lower ∧ (cell12416 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12416 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12416 ⟨31,by decide⟩).lower ∧ (cell12416 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12416 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12416 ⟨32,by decide⟩).lower ∧ (cell12416 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12416 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12416 ⟨33,by decide⟩).lower ∧ (cell12416 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12416 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12416 ⟨34,by decide⟩).lower ∧ (cell12416 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12416 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12416 ⟨35,by decide⟩).lower ∧ (cell12416 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12416 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12416 ⟨36,by decide⟩).lower ∧ (cell12416 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12416 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12416 ⟨37,by decide⟩).lower ∧ (cell12416 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12416 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12416 ⟨38,by decide⟩).lower ∧ (cell12416 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12416 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12416 ⟨39,by decide⟩).lower ∧ (cell12416 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12416 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12416 ⟨40,by decide⟩).lower ∧ (cell12416 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12416 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12416 ⟨41,by decide⟩).lower ∧ (cell12416 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12416 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12416 ⟨42,by decide⟩).lower ∧ (cell12416 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12416 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12416 ⟨43,by decide⟩).lower ∧ (cell12416 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12416 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12416 ⟨44,by decide⟩).lower ∧ (cell12416 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12416 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12416 ⟨45,by decide⟩).lower ∧ (cell12416 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12416 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12416 ⟨46,by decide⟩).lower ∧ (cell12416 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12416 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12416 ⟨47,by decide⟩).lower ∧ (cell12416 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12416 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12416 ⟨48,by decide⟩).lower ∧ (cell12416 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12416 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12416 ⟨49,by decide⟩).lower ∧ (cell12416 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12416 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12416 ⟨50,by decide⟩).lower ∧ (cell12416 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12416 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12416 ⟨51,by decide⟩).lower ∧ (cell12416 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12416 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12416 ⟨52,by decide⟩).lower ∧ (cell12416 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12416 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12416 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12416 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12416,cell12416,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12416 i).lower ∧
    (cell12416 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12416 i).upper ≤ (0.532 : ℝ) ∧
    (cell12416 i).centre ≤ (0.1 : ℝ) ∧ (cell12416 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12416 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12416 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12416

/-! The local source numeric instances at 12416 have no network premises. -/
namespace BstLean.Part269.N12416
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12416)
open BstLean.Part268 (cell12416)

noncomputable def sourceNumerics12416 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12416 (cell12416 i)
      scalarRow12416.M scalarRow12416.H scalarRow12416.xi := by
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
    energy_allowance := scalarRow12416.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12416]
    centre_nonneg := (scalarRow12416.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12416])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12416
/-! Actual 12417 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12417
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12417 ≤ (1.036218601391 : ℝ) := by
  have hr : (111.431593365616 : ℝ) ≤ √(12417 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.431593365616 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12417 12417 (11 / 1000) ≤
    (0.008578241448 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12417) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.431593365616 : ℝ) ≤ √(12417 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12417)
  have hdiv : K / √(12417 : ℝ) ≤ K / 111.431593365616 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.431593365616 ≤ (0.008578241448 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12417.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12417 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12417 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12417 := gPlus_lower 12417
end BstLean.Part269.N12417

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12417
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036218601390 : ℝ) ≤ wn 12417 := by
  have hn : √(12417 : ℝ) ≤ 111.431593365617 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12417 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.431593365617 ≤ 2 / √(12417 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257723389 : ℝ) ≤ rhoBar 12417 BstLean.Part154.csC ∧
    rhoBar 12417 BstLean.Part154.csC ≤ 0.000257723788 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036218601390 : ℝ) / (1.295212 * 12417) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036218601391 : ℝ) / (1.29521 * 12417) := by gcongr
      _ ≤ (0.000257723788 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12417 BstLean.Part154.csC) ≤ 0.001030961574 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12417 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12417 BstLean.Part154.csC) (piBar (rhoBar 12417 BstLean.Part154.csC)) ≤ 0.000196851380 ∧
    cc1 (rhoBar 12417 BstLean.Part154.csC) (piBar (rhoBar 12417 BstLean.Part154.csC)) ≤ 0.000125257797 ∧
    cc2 (rhoBar 12417 BstLean.Part154.csC) ≤ 0.000072713058 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12417 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12417 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12417 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12417 BstLean.Part154.csC * nuR (rhoBar 12417 BstLean.Part154.csC)) ≤ 0.000515464182 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257723788 : ℝ) * 0.001030961574 := by gcongr
      _ ≤ (0.000515464182 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12417 BstLean.Part154.csC) * nuR (rhoBar 12417 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001030961574 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12417 BstLean.Part154.csC) * rhoBar 12417 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257723788 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257723788 / 2 + 0.399 * 0.001030961574 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196851380 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515464182 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125257797 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257723788 / 1.414213562 := by gcongr
      _ ≤ (0.000072713058 : ℝ) := by norm_num

end BstLean.Part269.N12417

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12417
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12417 BstLean.Part154.csC) (piBar (rhoBar 12417 BstLean.Part154.csC)) ≤ 1.67345E-7 := by
  have hr0 : 0 ≤ rhoBar 12417 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12417 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12417 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12417 BstLean.Part154.csC) (piBar (rhoBar 12417 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12417 BstLean.Part154.csC) (piBar (rhoBar 12417 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12417 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196851380 : ℝ) ^ 2 + 0.000125257797 ^ 2 + 3 * 0.000072713058 ^ 2 +
        2 * 0.797885 * 0.000196851380 * 0.000125257797 + 2 * 0.000196851380 * 0.000072713058 +
        4 * 0.797885 * 0.000125257797 * 0.000072713058 := by gcongr
    _ ≤ (1.67345E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12417 BstLean.Part154.csC Θ ≤ 0.002691350638 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12417 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12417 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12417 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12417 BstLean.Part154.csC) (piBar (rhoBar 12417 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12417 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036218601391 * 1.67345E-7 / (0.000257723389 : ℝ) := by gcongr
    _ ≤ 0.002691350638 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12417 BstLean.Part154.csC Θ ≤ 0.002987371667 + 0.000680058221 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12417 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12417 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12417 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036218601391 : ℝ) * ((2 * Θ * 0.000257723788 +
        (6863 / 10000) * 0.000257723788 * 12417 * 0.001030961574) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002987371667 + 0.000680058221 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12417 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12417 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12417 0.011 Θ ∧ gammaRatio 12417 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12417 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036218601391 : ℝ) * 0.525 / ((1 - 0.011) * 12417) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12417 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12417 0.011 Θ) :=
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
    badAllowance 12417 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12417 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12417 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12417 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12417 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12417 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12417 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12417 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12417 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12417 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12417 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036218601391 : ℝ) * 12417 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12417 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004087371667 + 0.003371408859 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12417

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12417
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12417 BstLean.Part154.csC) (piBar (rhoBar 12417 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12417 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12417 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12417 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12417 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12417 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12417 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12417 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12417 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12417 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12417 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12417 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12417 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12417 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12417 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053085558958 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12417) ≤ 0.010717226103 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12417 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036218601391)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010717226103 + 2 * 0.737676 / 12417) := by gcongr
    _ ≤ (0.053085558958 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12417 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12417

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12417
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490478505 : ℝ) ≤ plow 12417 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12417) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053363961318)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412959085) : eMP 12417 0.011 xi bn ≤ 0.001216091226 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12417 : ℝ) * (1 - 0.011))) ≤ 0.000601219790 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001412959085 / (12417 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601219790 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601219790 : ℝ) + 3.141593 * 0.053363961318 / (12417 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001216091226 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053363961318)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412959085) : PiBarMP 12417 12 0.011 xi bn ≤ 0.163099165998 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12417 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037589348026 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.817024865315 : ℝ) ≤ √((12417 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.431593365616 : ℝ) ≤ √(12417 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12417) ≤ 0.125031042292 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037589348026 + 0.053363961318 * 1.772454 / (2 * (110.817024865315 : ℝ))) * (1 + 0.001216091226) +
        8 / (12417 * 111.431593365616) + 0.125031042292 := by gcongr
    _ ≤ (0.163099165998 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053363961318)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412959085) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284091968649) :
    parallelOracle 12417 0.011 xi bn cd ≤ 0.164116223637 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12417 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12417 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490478505 : ℝ) ≤ plow 12417 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.431593365616 : ℝ) ≤ √(12417 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284091968649 : ℝ) / (2 * 0.560490478505 * 111.431593365616)) * 0.163099165998 +
        0.284091968649 ^ 2 / (2 * 0.560490478505 * 111.431593365616) := by gcongr
    _ ≤ (0.164116223637 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053363961318) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412959085)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284091968649) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12417 12417 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490478505 : ℝ) ≤ plow 12417 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.431593365616 : ℝ) ≤ √(12417 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12417 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12417 Θ 1.22 ≤ 0.011900579180 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.431593365616 := by gcongr <;> linarith
      _ ≤ (0.011900579180 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12417 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12417 12417 0.011 ≤ 0.008578241448 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12417 12417 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12417 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12417 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12417 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12417 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164116223637 + 0.011900579180 + (0.008578241448 : ℝ) *
        (1 + 2 * (0.284091968649 + 0.011900579180) / (0.560490478505 * 111.431593365616))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12417]

end BstLean.Part269.N12417

/-! The original eight local profiles supply actual 12417 moment certificates. -/
namespace BstLean.Part269.N12417
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12417 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12417 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12417 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053363961318 ∧
    0 ≤ bN 12417 BstLean.Part154.csC (groupTheta g) ∧ bN 12417 BstLean.Part154.csC (groupTheta g) ≤ 0.001412959085 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12417 12417 0.011
      (momentAllowance 12417 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12417 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12417 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12417 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12417 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12417 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231006409691 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12417 0.011
      (momentAllowance 12417 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12417 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12417
/-! The actual computed-centre upper energy formula at 12417. -/
namespace BstLean.Part269.N12417
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12417

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12417
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12417)
open BstLean.Part268 (cell12417)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086363530120
  | 2 => 0.087323464341
  | 3 => 0.088284224335
  | 4 => 0.089247832832
  | 5 => 0.090216714013
  | 6 => 0.091193750139
  | 7 => 0.092182342979
  | 8 => 0.093186479977
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12417 12417 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12417 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12417

/-! Actual upper energy certificates on all 43 source endpoints at 12417. -/
namespace BstLean.Part269.N12417
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12417)
open BstLean.Part268 (cell12417)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12417 (gMinus 12417) (1 - (cell12417 i).lower) ≤ 1 ∧
    energyUpper 12417 (gMinus 12417) (BstLean.Part211.gPlus 12417)
      (finiteEnergy 12417 12417 0.011) (1 - (cell12417 i).lower) ≤
      (cell12417 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨10,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨11,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨12,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨13,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨14,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨15,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨16,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨17,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨18,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨19,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨20,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨21,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨22,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨23,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨24,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨25,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨26,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨27,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨28,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨29,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨30,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨31,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨32,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨33,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨34,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨35,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨36,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨37,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨38,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨39,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨40,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨41,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨42,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨43,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨44,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨45,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨46,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨47,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨48,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨49,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨50,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨51,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12417) (by norm_num)
        (q := 1 - (cell12417 ⟨52,by decide⟩).lower)
        (by norm_num [cell12417]) (by norm_num [cell12417])
      exact ⟨E.1,E.2.trans (by norm_num [cell12417])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12417

/-! Source-cell containment and simple scalar guards at 12417. -/
namespace BstLean.Part269.N12417
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12417)
open BstLean.Part268 (cell12417)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12417 ⟨10,by decide⟩).lower ∧ (cell12417 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12417 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12417 ⟨11,by decide⟩).lower ∧ (cell12417 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12417 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12417 ⟨12,by decide⟩).lower ∧ (cell12417 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12417 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12417 ⟨13,by decide⟩).lower ∧ (cell12417 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12417 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12417 ⟨14,by decide⟩).lower ∧ (cell12417 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12417 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12417 ⟨15,by decide⟩).lower ∧ (cell12417 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12417 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12417 ⟨16,by decide⟩).lower ∧ (cell12417 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12417 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12417 ⟨17,by decide⟩).lower ∧ (cell12417 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12417 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12417 ⟨18,by decide⟩).lower ∧ (cell12417 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12417 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12417 ⟨19,by decide⟩).lower ∧ (cell12417 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12417 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12417 ⟨20,by decide⟩).lower ∧ (cell12417 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12417 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12417 ⟨21,by decide⟩).lower ∧ (cell12417 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12417 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12417 ⟨22,by decide⟩).lower ∧ (cell12417 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12417 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12417 ⟨23,by decide⟩).lower ∧ (cell12417 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12417 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12417 ⟨24,by decide⟩).lower ∧ (cell12417 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12417 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12417 ⟨25,by decide⟩).lower ∧ (cell12417 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12417 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12417 ⟨26,by decide⟩).lower ∧ (cell12417 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12417 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12417 ⟨27,by decide⟩).lower ∧ (cell12417 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12417 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12417 ⟨28,by decide⟩).lower ∧ (cell12417 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12417 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12417 ⟨29,by decide⟩).lower ∧ (cell12417 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12417 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12417 ⟨30,by decide⟩).lower ∧ (cell12417 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12417 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12417 ⟨31,by decide⟩).lower ∧ (cell12417 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12417 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12417 ⟨32,by decide⟩).lower ∧ (cell12417 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12417 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12417 ⟨33,by decide⟩).lower ∧ (cell12417 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12417 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12417 ⟨34,by decide⟩).lower ∧ (cell12417 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12417 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12417 ⟨35,by decide⟩).lower ∧ (cell12417 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12417 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12417 ⟨36,by decide⟩).lower ∧ (cell12417 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12417 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12417 ⟨37,by decide⟩).lower ∧ (cell12417 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12417 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12417 ⟨38,by decide⟩).lower ∧ (cell12417 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12417 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12417 ⟨39,by decide⟩).lower ∧ (cell12417 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12417 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12417 ⟨40,by decide⟩).lower ∧ (cell12417 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12417 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12417 ⟨41,by decide⟩).lower ∧ (cell12417 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12417 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12417 ⟨42,by decide⟩).lower ∧ (cell12417 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12417 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12417 ⟨43,by decide⟩).lower ∧ (cell12417 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12417 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12417 ⟨44,by decide⟩).lower ∧ (cell12417 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12417 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12417 ⟨45,by decide⟩).lower ∧ (cell12417 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12417 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12417 ⟨46,by decide⟩).lower ∧ (cell12417 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12417 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12417 ⟨47,by decide⟩).lower ∧ (cell12417 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12417 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12417 ⟨48,by decide⟩).lower ∧ (cell12417 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12417 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12417 ⟨49,by decide⟩).lower ∧ (cell12417 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12417 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12417 ⟨50,by decide⟩).lower ∧ (cell12417 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12417 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12417 ⟨51,by decide⟩).lower ∧ (cell12417 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12417 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12417 ⟨52,by decide⟩).lower ∧ (cell12417 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12417 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12417 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12417 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12417,cell12417,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12417 i).lower ∧
    (cell12417 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12417 i).upper ≤ (0.532 : ℝ) ∧
    (cell12417 i).centre ≤ (0.1 : ℝ) ∧ (cell12417 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12417 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12417 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12417

/-! The local source numeric instances at 12417 have no network premises. -/
namespace BstLean.Part269.N12417
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12417)
open BstLean.Part268 (cell12417)

noncomputable def sourceNumerics12417 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12417 (cell12417 i)
      scalarRow12417.M scalarRow12417.H scalarRow12417.xi := by
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
    energy_allowance := scalarRow12417.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12417]
    centre_nonneg := (scalarRow12417.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12417])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12417
/-! Actual 12418 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12418
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12418 ≤ (1.036217130080 : ℝ) := by
  have hr : (111.436080333077 : ℝ) ≤ √(12418 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.436080333077 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12418 12418 (11 / 1000) ≤
    (0.008577896043 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12418) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.436080333077 : ℝ) ≤ √(12418 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12418)
  have hdiv : K / √(12418 : ℝ) ≤ K / 111.436080333077 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.436080333077 ≤ (0.008577896043 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12418.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12418 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12418 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12418 := gPlus_lower 12418
end BstLean.Part269.N12418

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12418
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036217130079 : ℝ) ≤ wn 12418 := by
  have hn : √(12418 : ℝ) ≤ 111.436080333078 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12418 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.436080333078 ≤ 2 / √(12418 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257702269 : ℝ) ≤ rhoBar 12418 BstLean.Part154.csC ∧
    rhoBar 12418 BstLean.Part154.csC ≤ 0.000257702668 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036217130079 : ℝ) / (1.295212 * 12418) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036217130080 : ℝ) / (1.29521 * 12418) := by gcongr
      _ ≤ (0.000257702668 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12418 BstLean.Part154.csC) ≤ 0.001030877083 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12418 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12418 BstLean.Part154.csC) (piBar (rhoBar 12418 BstLean.Part154.csC)) ≤ 0.000196835248 ∧
    cc1 (rhoBar 12418 BstLean.Part154.csC) (piBar (rhoBar 12418 BstLean.Part154.csC)) ≤ 0.000125247532 ∧
    cc2 (rhoBar 12418 BstLean.Part154.csC) ≤ 0.000072707099 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12418 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12418 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12418 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12418 BstLean.Part154.csC * nuR (rhoBar 12418 BstLean.Part154.csC)) ≤ 0.000515421939 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257702668 : ℝ) * 0.001030877083 := by gcongr
      _ ≤ (0.000515421939 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12418 BstLean.Part154.csC) * nuR (rhoBar 12418 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001030877083 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12418 BstLean.Part154.csC) * rhoBar 12418 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257702668 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257702668 / 2 + 0.399 * 0.001030877083 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196835248 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515421939 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125247532 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257702668 / 1.414213562 := by gcongr
      _ ≤ (0.000072707099 : ℝ) := by norm_num

end BstLean.Part269.N12418

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12418
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12418 BstLean.Part154.csC) (piBar (rhoBar 12418 BstLean.Part154.csC)) ≤ 1.67317E-7 := by
  have hr0 : 0 ≤ rhoBar 12418 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12418 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12418 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12418 BstLean.Part154.csC) (piBar (rhoBar 12418 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12418 BstLean.Part154.csC) (piBar (rhoBar 12418 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12418 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196835248 : ℝ) ^ 2 + 0.000125247532 ^ 2 + 3 * 0.000072707099 ^ 2 +
        2 * 0.797885 * 0.000196835248 * 0.000125247532 + 2 * 0.000196835248 * 0.000072707099 +
        4 * 0.797885 * 0.000125247532 * 0.000072707099 := by gcongr
    _ ≤ (1.67317E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12418 BstLean.Part154.csC Θ ≤ 0.002691117036 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12418 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12418 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12418 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12418 BstLean.Part154.csC) (piBar (rhoBar 12418 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12418 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036217130080 * 1.67317E-7 / (0.000257702269 : ℝ) := by gcongr
    _ ≤ 0.002691117036 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12418 BstLean.Part154.csC Θ ≤ 0.002987118358 + 0.000680001526 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12418 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12418 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12418 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036217130080 : ℝ) * ((2 * Θ * 0.000257702668 +
        (6863 / 10000) * 0.000257702668 * 12418 * 0.001030877083) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002987118358 + 0.000680001526 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12418 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12418 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12418 0.011 Θ ∧ gammaRatio 12418 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12418 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036217130080 : ℝ) * 0.525 / ((1 - 0.011) * 12418) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12418 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12418 0.011 Θ) :=
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
    badAllowance 12418 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12418 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12418 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12418 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12418 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12418 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12418 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12418 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12418 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12418 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12418 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036217130080 : ℝ) * 12418 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12418 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004087118358 + 0.003371118562 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12418

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12418
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12418 BstLean.Part154.csC) (piBar (rhoBar 12418 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12418 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12418 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12418 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12418 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12418 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12418 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12418 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12418 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12418 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12418 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12418 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12418 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12418 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12418 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053083398032 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12418) ≤ 0.010716794574 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12418 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036217130080)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010716794574 + 2 * 0.737676 / 12418) := by gcongr
    _ ≤ (0.053083398032 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12418 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12418

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12418
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490525809 : ℝ) ≤ plow 12418 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12418) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053363555604)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412836444) : eMP 12418 0.011 xi bn ≤ 0.001215989423 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12418 : ℝ) * (1 - 0.011))) ≤ 0.000601169490 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001412836444 / (12418 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601169490 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601169490 : ℝ) + 3.141593 * 0.053363555604 / (12418 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001215989423 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053363555604)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412836444) : PiBarMP 12418 12 0.011 xi bn ≤ 0.163092473264 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12418 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037587716664 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.821487086214 : ℝ) ≤ √((12418 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.436080333077 : ℝ) ≤ √(12418 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12418) ≤ 0.125026007925 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037587716664 + 0.053363555604 * 1.772454 / (2 * (110.821487086214 : ℝ))) * (1 + 0.001215989423) +
        8 / (12418 * 111.436080333077) + 0.125026007925 := by gcongr
    _ ≤ (0.163092473264 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053363555604)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412836444) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284088929577) :
    parallelOracle 12418 0.011 xi bn cd ≤ 0.164109456854 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12418 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12418 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490525809 : ℝ) ≤ plow 12418 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.436080333077 : ℝ) ≤ √(12418 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284088929577 : ℝ) / (2 * 0.560490525809 * 111.436080333077)) * 0.163092473264 +
        0.284088929577 ^ 2 / (2 * 0.560490525809 * 111.436080333077) := by gcongr
    _ ≤ (0.164109456854 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053363555604) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412836444)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284088929577) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12418 12418 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490525809 : ℝ) ≤ plow 12418 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.436080333077 : ℝ) ≤ √(12418 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12418 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12418 Θ 1.22 ≤ 0.011900100004 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.436080333077 := by gcongr <;> linarith
      _ ≤ (0.011900100004 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12418 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12418 12418 0.011 ≤ 0.008577896043 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12418 12418 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12418 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12418 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12418 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12418 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164109456854 + 0.011900100004 + (0.008577896043 : ℝ) *
        (1 + 2 * (0.284088929577 + 0.011900100004) / (0.560490525809 * 111.436080333077))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12418]

end BstLean.Part269.N12418

/-! The original eight local profiles supply actual 12418 moment certificates. -/
namespace BstLean.Part269.N12418
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12418 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12418 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12418 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053363555604 ∧
    0 ≤ bN 12418 BstLean.Part154.csC (groupTheta g) ∧ bN 12418 BstLean.Part154.csC (groupTheta g) ≤ 0.001412836444 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12418 12418 0.011
      (momentAllowance 12418 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12418 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12418 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12418 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12418 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12418 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231005531545 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12418 0.011
      (momentAllowance 12418 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12418 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12418
/-! The actual computed-centre upper energy formula at 12418. -/
namespace BstLean.Part269.N12418
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12418

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12418
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12418)
open BstLean.Part268 (cell12418)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086360257935
  | 2 => 0.087320123382
  | 3 => 0.088280803227
  | 4 => 0.089244317693
  | 5 => 0.090213088026
  | 6 => 0.091189993083
  | 7 => 0.092178430703
  | 8 => 0.093182383825
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12418 12418 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12418 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12418

/-! Actual upper energy certificates on all 43 source endpoints at 12418. -/
namespace BstLean.Part269.N12418
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12418)
open BstLean.Part268 (cell12418)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12418 (gMinus 12418) (1 - (cell12418 i).lower) ≤ 1 ∧
    energyUpper 12418 (gMinus 12418) (BstLean.Part211.gPlus 12418)
      (finiteEnergy 12418 12418 0.011) (1 - (cell12418 i).lower) ≤
      (cell12418 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨10,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨11,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨12,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨13,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨14,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨15,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨16,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨17,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨18,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨19,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨20,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨21,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨22,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨23,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨24,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨25,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨26,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨27,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨28,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨29,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨30,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨31,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨32,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨33,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨34,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨35,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨36,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨37,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨38,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨39,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨40,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨41,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨42,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨43,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨44,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨45,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨46,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨47,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨48,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨49,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨50,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨51,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12418) (by norm_num)
        (q := 1 - (cell12418 ⟨52,by decide⟩).lower)
        (by norm_num [cell12418]) (by norm_num [cell12418])
      exact ⟨E.1,E.2.trans (by norm_num [cell12418])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12418

/-! Source-cell containment and simple scalar guards at 12418. -/
namespace BstLean.Part269.N12418
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12418)
open BstLean.Part268 (cell12418)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12418 ⟨10,by decide⟩).lower ∧ (cell12418 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12418 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12418 ⟨11,by decide⟩).lower ∧ (cell12418 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12418 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12418 ⟨12,by decide⟩).lower ∧ (cell12418 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12418 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12418 ⟨13,by decide⟩).lower ∧ (cell12418 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12418 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12418 ⟨14,by decide⟩).lower ∧ (cell12418 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12418 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12418 ⟨15,by decide⟩).lower ∧ (cell12418 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12418 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12418 ⟨16,by decide⟩).lower ∧ (cell12418 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12418 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12418 ⟨17,by decide⟩).lower ∧ (cell12418 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12418 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12418 ⟨18,by decide⟩).lower ∧ (cell12418 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12418 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12418 ⟨19,by decide⟩).lower ∧ (cell12418 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12418 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12418 ⟨20,by decide⟩).lower ∧ (cell12418 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12418 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12418 ⟨21,by decide⟩).lower ∧ (cell12418 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12418 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12418 ⟨22,by decide⟩).lower ∧ (cell12418 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12418 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12418 ⟨23,by decide⟩).lower ∧ (cell12418 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12418 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12418 ⟨24,by decide⟩).lower ∧ (cell12418 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12418 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12418 ⟨25,by decide⟩).lower ∧ (cell12418 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12418 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12418 ⟨26,by decide⟩).lower ∧ (cell12418 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12418 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12418 ⟨27,by decide⟩).lower ∧ (cell12418 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12418 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12418 ⟨28,by decide⟩).lower ∧ (cell12418 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12418 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12418 ⟨29,by decide⟩).lower ∧ (cell12418 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12418 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12418 ⟨30,by decide⟩).lower ∧ (cell12418 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12418 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12418 ⟨31,by decide⟩).lower ∧ (cell12418 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12418 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12418 ⟨32,by decide⟩).lower ∧ (cell12418 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12418 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12418 ⟨33,by decide⟩).lower ∧ (cell12418 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12418 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12418 ⟨34,by decide⟩).lower ∧ (cell12418 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12418 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12418 ⟨35,by decide⟩).lower ∧ (cell12418 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12418 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12418 ⟨36,by decide⟩).lower ∧ (cell12418 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12418 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12418 ⟨37,by decide⟩).lower ∧ (cell12418 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12418 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12418 ⟨38,by decide⟩).lower ∧ (cell12418 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12418 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12418 ⟨39,by decide⟩).lower ∧ (cell12418 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12418 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12418 ⟨40,by decide⟩).lower ∧ (cell12418 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12418 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12418 ⟨41,by decide⟩).lower ∧ (cell12418 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12418 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12418 ⟨42,by decide⟩).lower ∧ (cell12418 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12418 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12418 ⟨43,by decide⟩).lower ∧ (cell12418 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12418 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12418 ⟨44,by decide⟩).lower ∧ (cell12418 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12418 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12418 ⟨45,by decide⟩).lower ∧ (cell12418 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12418 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12418 ⟨46,by decide⟩).lower ∧ (cell12418 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12418 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12418 ⟨47,by decide⟩).lower ∧ (cell12418 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12418 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12418 ⟨48,by decide⟩).lower ∧ (cell12418 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12418 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12418 ⟨49,by decide⟩).lower ∧ (cell12418 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12418 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12418 ⟨50,by decide⟩).lower ∧ (cell12418 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12418 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12418 ⟨51,by decide⟩).lower ∧ (cell12418 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12418 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12418 ⟨52,by decide⟩).lower ∧ (cell12418 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12418 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12418 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12418 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12418,cell12418,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12418 i).lower ∧
    (cell12418 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12418 i).upper ≤ (0.532 : ℝ) ∧
    (cell12418 i).centre ≤ (0.1 : ℝ) ∧ (cell12418 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12418 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12418 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12418

/-! The local source numeric instances at 12418 have no network premises. -/
namespace BstLean.Part269.N12418
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12418)
open BstLean.Part268 (cell12418)

noncomputable def sourceNumerics12418 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12418 (cell12418 i)
      scalarRow12418.M scalarRow12418.H scalarRow12418.xi := by
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
    energy_allowance := scalarRow12418.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12418]
    centre_nonneg := (scalarRow12418.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12418])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12418
/-! Actual 12419 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12419
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12419 ≤ (1.036215658949 : ℝ) := by
  have hr : (111.440567119877 : ℝ) ≤ √(12419 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.440567119877 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12419 12419 (11 / 1000) ≤
    (0.008577550680 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12419) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.440567119877 : ℝ) ≤ √(12419 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12419)
  have hdiv : K / √(12419 : ℝ) ≤ K / 111.440567119877 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.440567119877 ≤ (0.008577550680 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12419.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12419 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12419 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12419 := gPlus_lower 12419
end BstLean.Part269.N12419

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12419
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036215658948 : ℝ) ≤ wn 12419 := by
  have hn : √(12419 : ℝ) ≤ 111.440567119878 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12419 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.440567119878 ≤ 2 / √(12419 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257681153 : ℝ) ≤ rhoBar 12419 BstLean.Part154.csC ∧
    rhoBar 12419 BstLean.Part154.csC ≤ 0.000257681552 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036215658948 : ℝ) / (1.295212 * 12419) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036215658949 : ℝ) / (1.29521 * 12419) := by gcongr
      _ ≤ (0.000257681552 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12419 BstLean.Part154.csC) ≤ 0.001030792608 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12419 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12419 BstLean.Part154.csC) (piBar (rhoBar 12419 BstLean.Part154.csC)) ≤ 0.000196819119 ∧
    cc1 (rhoBar 12419 BstLean.Part154.csC) (piBar (rhoBar 12419 BstLean.Part154.csC)) ≤ 0.000125237269 ∧
    cc2 (rhoBar 12419 BstLean.Part154.csC) ≤ 0.000072701141 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12419 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12419 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12419 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12419 BstLean.Part154.csC * nuR (rhoBar 12419 BstLean.Part154.csC)) ≤ 0.000515379704 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257681552 : ℝ) * 0.001030792608 := by gcongr
      _ ≤ (0.000515379704 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12419 BstLean.Part154.csC) * nuR (rhoBar 12419 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001030792608 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12419 BstLean.Part154.csC) * rhoBar 12419 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257681552 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257681552 / 2 + 0.399 * 0.001030792608 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196819119 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515379704 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125237269 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257681552 / 1.414213562 := by gcongr
      _ ≤ (0.000072701141 : ℝ) := by norm_num

end BstLean.Part269.N12419

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12419
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12419 BstLean.Part154.csC) (piBar (rhoBar 12419 BstLean.Part154.csC)) ≤ 1.67290E-7 := by
  have hr0 : 0 ≤ rhoBar 12419 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12419 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12419 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12419 BstLean.Part154.csC) (piBar (rhoBar 12419 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12419 BstLean.Part154.csC) (piBar (rhoBar 12419 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12419 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196819119 : ℝ) ^ 2 + 0.000125237269 ^ 2 + 3 * 0.000072701141 ^ 2 +
        2 * 0.797885 * 0.000196819119 * 0.000125237269 + 2 * 0.000196819119 * 0.000072701141 +
        4 * 0.797885 * 0.000125237269 * 0.000072701141 := by gcongr
    _ ≤ (1.67290E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12419 BstLean.Part154.csC Θ ≤ 0.002690899441 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12419 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12419 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12419 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12419 BstLean.Part154.csC) (piBar (rhoBar 12419 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12419 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036215658949 * 1.67290E-7 / (0.000257681153 : ℝ) := by gcongr
    _ ≤ 0.002690899441 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12419 BstLean.Part154.csC Θ ≤ 0.002986865104 + 0.000679944842 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12419 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12419 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12419 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036215658949 : ℝ) * ((2 * Θ * 0.000257681552 +
        (6863 / 10000) * 0.000257681552 * 12419 * 0.001030792608) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002986865104 + 0.000679944842 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12419 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12419 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12419 0.011 Θ ∧ gammaRatio 12419 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12419 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036215658949 : ℝ) * 0.525 / ((1 - 0.011) * 12419) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12419 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12419 0.011 Θ) :=
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
    badAllowance 12419 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12419 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12419 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12419 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12419 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12419 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12419 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12419 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12419 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12419 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12419 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036215658949 : ℝ) * 12419 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12419 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004086865104 + 0.003370844283 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12419

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12419
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12419 BstLean.Part154.csC) (piBar (rhoBar 12419 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12419 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12419 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12419 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12419 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12419 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12419 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12419 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12419 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12419 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12419 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12419 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12419 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12419 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12419 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053081237374 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12419) ≤ 0.010716363098 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12419 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036215658949)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010716363098 + 2 * 0.737676 / 12419) := by gcongr
    _ ≤ (0.053081237374 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12419 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12419

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12419
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490573105 : ℝ) ≤ plow 12419 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12419) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053363158353)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412722207) : eMP 12419 0.011 xi bn ≤ 0.001215891206 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12419 : ℝ) * (1 - 0.011))) ≤ 0.000601120982 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001412722207 / (12419 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601120982 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601120982 : ℝ) + 3.141593 * 0.053363158353 / (12419 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001215891206 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053363158353)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412722207) : PiBarMP 12419 12 0.011 xi bn ≤ 0.163085893206 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12419 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037586197028 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.825949127449 : ℝ) ≤ √((12419 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.440567119877 : ℝ) ≤ √(12419 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12419) ≤ 0.125020974165 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037586197028 + 0.053363158353 * 1.772454 / (2 * (110.825949127449 : ℝ))) * (1 + 0.001215891206) +
        8 / (12419 * 111.440567119877) + 0.125020974165 := by gcongr
    _ ≤ (0.163085893206 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053363158353)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412722207) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284085909087) :
    parallelOracle 12419 0.011 xi bn cd ≤ 0.164102803120 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12419 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12419 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490573105 : ℝ) ≤ plow 12419 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.440567119877 : ℝ) ≤ √(12419 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284085909087 : ℝ) / (2 * 0.560490573105 * 111.440567119877)) * 0.163085893206 +
        0.284085909087 ^ 2 / (2 * 0.560490573105 * 111.440567119877) := by gcongr
    _ ≤ (0.164102803120 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053363158353) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412722207)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284085909087) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12419 12419 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490573105 : ℝ) ≤ plow 12419 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.440567119877 : ℝ) ≤ √(12419 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12419 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12419 Θ 1.22 ≤ 0.011899620886 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.440567119877 := by gcongr <;> linarith
      _ ≤ (0.011899620886 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12419 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12419 12419 0.011 ≤ 0.008577550680 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12419 12419 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12419 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12419 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12419 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12419 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164102803120 + 0.011899620886 + (0.008577550680 : ℝ) *
        (1 + 2 * (0.284085909087 + 0.011899620886) / (0.560490573105 * 111.440567119877))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12419]

end BstLean.Part269.N12419

/-! The original eight local profiles supply actual 12419 moment certificates. -/
namespace BstLean.Part269.N12419
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12419 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12419 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12419 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053363158353 ∧
    0 ≤ bN 12419 BstLean.Part154.csC (groupTheta g) ∧ bN 12419 BstLean.Part154.csC (groupTheta g) ≤ 0.001412722207 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12419 12419 0.011
      (momentAllowance 12419 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12419 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12419 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12419 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12419 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12419 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231004671713 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12419 0.011
      (momentAllowance 12419 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12419 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12419
/-! The actual computed-centre upper energy formula at 12419. -/
namespace BstLean.Part269.N12419
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12419

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12419
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12419)
open BstLean.Part268 (cell12419)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086356987208
  | 2 => 0.087316783944
  | 3 => 0.088277383721
  | 4 => 0.089240804252
  | 5 => 0.090209463857
  | 6 => 0.091186237988
  | 7 => 0.092174520562
  | 8 => 0.093178290013
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12419 12419 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12419 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12419

/-! Actual upper energy certificates on all 43 source endpoints at 12419. -/
namespace BstLean.Part269.N12419
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12419)
open BstLean.Part268 (cell12419)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12419 (gMinus 12419) (1 - (cell12419 i).lower) ≤ 1 ∧
    energyUpper 12419 (gMinus 12419) (BstLean.Part211.gPlus 12419)
      (finiteEnergy 12419 12419 0.011) (1 - (cell12419 i).lower) ≤
      (cell12419 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨10,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨11,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨12,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨13,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨14,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨15,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨16,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨17,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨18,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨19,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨20,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨21,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨22,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨23,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨24,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨25,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨26,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨27,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨28,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨29,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨30,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨31,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨32,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨33,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨34,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨35,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨36,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨37,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨38,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨39,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨40,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨41,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨42,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨43,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨44,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨45,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨46,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨47,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨48,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨49,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨50,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨51,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12419) (by norm_num)
        (q := 1 - (cell12419 ⟨52,by decide⟩).lower)
        (by norm_num [cell12419]) (by norm_num [cell12419])
      exact ⟨E.1,E.2.trans (by norm_num [cell12419])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12419

/-! Source-cell containment and simple scalar guards at 12419. -/
namespace BstLean.Part269.N12419
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12419)
open BstLean.Part268 (cell12419)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12419 ⟨10,by decide⟩).lower ∧ (cell12419 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12419 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12419 ⟨11,by decide⟩).lower ∧ (cell12419 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12419 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12419 ⟨12,by decide⟩).lower ∧ (cell12419 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12419 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12419 ⟨13,by decide⟩).lower ∧ (cell12419 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12419 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12419 ⟨14,by decide⟩).lower ∧ (cell12419 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12419 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12419 ⟨15,by decide⟩).lower ∧ (cell12419 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12419 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12419 ⟨16,by decide⟩).lower ∧ (cell12419 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12419 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12419 ⟨17,by decide⟩).lower ∧ (cell12419 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12419 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12419 ⟨18,by decide⟩).lower ∧ (cell12419 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12419 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12419 ⟨19,by decide⟩).lower ∧ (cell12419 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12419 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12419 ⟨20,by decide⟩).lower ∧ (cell12419 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12419 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12419 ⟨21,by decide⟩).lower ∧ (cell12419 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12419 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12419 ⟨22,by decide⟩).lower ∧ (cell12419 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12419 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12419 ⟨23,by decide⟩).lower ∧ (cell12419 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12419 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12419 ⟨24,by decide⟩).lower ∧ (cell12419 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12419 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12419 ⟨25,by decide⟩).lower ∧ (cell12419 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12419 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12419 ⟨26,by decide⟩).lower ∧ (cell12419 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12419 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12419 ⟨27,by decide⟩).lower ∧ (cell12419 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12419 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12419 ⟨28,by decide⟩).lower ∧ (cell12419 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12419 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12419 ⟨29,by decide⟩).lower ∧ (cell12419 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12419 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12419 ⟨30,by decide⟩).lower ∧ (cell12419 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12419 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12419 ⟨31,by decide⟩).lower ∧ (cell12419 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12419 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12419 ⟨32,by decide⟩).lower ∧ (cell12419 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12419 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12419 ⟨33,by decide⟩).lower ∧ (cell12419 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12419 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12419 ⟨34,by decide⟩).lower ∧ (cell12419 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12419 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12419 ⟨35,by decide⟩).lower ∧ (cell12419 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12419 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12419 ⟨36,by decide⟩).lower ∧ (cell12419 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12419 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12419 ⟨37,by decide⟩).lower ∧ (cell12419 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12419 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12419 ⟨38,by decide⟩).lower ∧ (cell12419 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12419 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12419 ⟨39,by decide⟩).lower ∧ (cell12419 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12419 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12419 ⟨40,by decide⟩).lower ∧ (cell12419 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12419 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12419 ⟨41,by decide⟩).lower ∧ (cell12419 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12419 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12419 ⟨42,by decide⟩).lower ∧ (cell12419 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12419 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12419 ⟨43,by decide⟩).lower ∧ (cell12419 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12419 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12419 ⟨44,by decide⟩).lower ∧ (cell12419 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12419 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12419 ⟨45,by decide⟩).lower ∧ (cell12419 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12419 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12419 ⟨46,by decide⟩).lower ∧ (cell12419 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12419 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12419 ⟨47,by decide⟩).lower ∧ (cell12419 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12419 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12419 ⟨48,by decide⟩).lower ∧ (cell12419 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12419 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12419 ⟨49,by decide⟩).lower ∧ (cell12419 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12419 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12419 ⟨50,by decide⟩).lower ∧ (cell12419 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12419 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12419 ⟨51,by decide⟩).lower ∧ (cell12419 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12419 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12419 ⟨52,by decide⟩).lower ∧ (cell12419 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12419 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12419 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12419 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12419,cell12419,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12419 i).lower ∧
    (cell12419 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12419 i).upper ≤ (0.532 : ℝ) ∧
    (cell12419 i).centre ≤ (0.1 : ℝ) ∧ (cell12419 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12419 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12419 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12419

/-! The local source numeric instances at 12419 have no network premises. -/
namespace BstLean.Part269.N12419
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12419)
open BstLean.Part268 (cell12419)

noncomputable def sourceNumerics12419 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12419 (cell12419 i)
      scalarRow12419.M scalarRow12419.H scalarRow12419.xi := by
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
    energy_allowance := scalarRow12419.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12419]
    centre_nonneg := (scalarRow12419.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12419])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12419
/-! Actual 12420 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12420
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12420 ≤ (1.036214187996 : ℝ) := by
  have hr : (111.445053726040 : ℝ) ≤ √(12420 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.445053726040 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12420 12420 (11 / 1000) ≤
    (0.008577205358 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12420) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.445053726040 : ℝ) ≤ √(12420 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12420)
  have hdiv : K / √(12420 : ℝ) ≤ K / 111.445053726040 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.445053726040 ≤ (0.008577205358 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12420.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12420 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12420 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12420 := gPlus_lower 12420
end BstLean.Part269.N12420

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12420
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036214187995 : ℝ) ≤ wn 12420 := by
  have hn : √(12420 : ℝ) ≤ 111.445053726041 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12420 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.445053726041 ≤ 2 / √(12420 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257660040 : ℝ) ≤ rhoBar 12420 BstLean.Part154.csC ∧
    rhoBar 12420 BstLean.Part154.csC ≤ 0.000257660439 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036214187995 : ℝ) / (1.295212 * 12420) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036214187996 : ℝ) / (1.29521 * 12420) := by gcongr
      _ ≤ (0.000257660439 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12420 BstLean.Part154.csC) ≤ 0.001030708145 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12420 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12420 BstLean.Part154.csC) (piBar (rhoBar 12420 BstLean.Part154.csC)) ≤ 0.000196802992 ∧
    cc1 (rhoBar 12420 BstLean.Part154.csC) (piBar (rhoBar 12420 BstLean.Part154.csC)) ≤ 0.000125227007 ∧
    cc2 (rhoBar 12420 BstLean.Part154.csC) ≤ 0.000072695185 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12420 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12420 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12420 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12420 BstLean.Part154.csC * nuR (rhoBar 12420 BstLean.Part154.csC)) ≤ 0.000515337475 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257660439 : ℝ) * 0.001030708145 := by gcongr
      _ ≤ (0.000515337475 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12420 BstLean.Part154.csC) * nuR (rhoBar 12420 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001030708145 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12420 BstLean.Part154.csC) * rhoBar 12420 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257660439 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257660439 / 2 + 0.399 * 0.001030708145 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196802992 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515337475 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125227007 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257660439 / 1.414213562 := by gcongr
      _ ≤ (0.000072695185 : ℝ) := by norm_num

end BstLean.Part269.N12420

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12420
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12420 BstLean.Part154.csC) (piBar (rhoBar 12420 BstLean.Part154.csC)) ≤ 1.67262E-7 := by
  have hr0 : 0 ≤ rhoBar 12420 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12420 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12420 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12420 BstLean.Part154.csC) (piBar (rhoBar 12420 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12420 BstLean.Part154.csC) (piBar (rhoBar 12420 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12420 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196802992 : ℝ) ^ 2 + 0.000125227007 ^ 2 + 3 * 0.000072695185 ^ 2 +
        2 * 0.797885 * 0.000196802992 * 0.000125227007 + 2 * 0.000196802992 * 0.000072695185 +
        4 * 0.797885 * 0.000125227007 * 0.000072695185 := by gcongr
    _ ≤ (1.67262E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12420 BstLean.Part154.csC Θ ≤ 0.002690665693 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12420 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12420 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12420 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12420 BstLean.Part154.csC) (piBar (rhoBar 12420 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12420 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036214187996 * 1.67262E-7 / (0.000257660040 : ℝ) := by gcongr
    _ ≤ 0.002690665693 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12420 BstLean.Part154.csC Θ ≤ 0.002986611882 + 0.000679888166 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12420 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12420 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12420 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036214187996 : ℝ) * ((2 * Θ * 0.000257660439 +
        (6863 / 10000) * 0.000257660439 * 12420 * 0.001030708145) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002986611882 + 0.000679888166 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12420 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12420 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12420 0.011 Θ ∧ gammaRatio 12420 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12420 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036214187996 : ℝ) * 0.525 / ((1 - 0.011) * 12420) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12420 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12420 0.011 Θ) :=
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
    badAllowance 12420 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12420 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12420 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12420 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12420 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12420 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12420 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12420 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12420 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12420 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12420 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036214187996 : ℝ) * 12420 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12420 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004086611882 + 0.003370553859 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12420

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12420
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12420 BstLean.Part154.csC) (piBar (rhoBar 12420 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12420 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12420 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12420 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12420 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12420 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12420 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12420 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12420 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12420 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12420 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12420 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12420 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12420 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12420 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053079076977 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12420) ≤ 0.010715931674 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12420 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036214187996)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010715931674 + 2 * 0.737676 / 12420) := by gcongr
    _ ≤ (0.053079076977 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12420 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12420

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12420
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490620394 : ℝ) ≤ plow 12420 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12420) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053362752658)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412599489) : eMP 12420 0.011 xi bn ≤ 0.001215789388 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12420 : ℝ) * (1 - 0.011))) ≤ 0.000601070674 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001412599489 / (12420 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601070674 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601070674 : ℝ) + 3.141593 * 0.053362752658 / (12420 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001215789388 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053362752658)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412599489) : PiBarMP 12420 12 0.011 xi bn ≤ 0.163079200529 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12420 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037584564505 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.830410989042 : ℝ) ≤ √((12420 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.445053726040 : ℝ) ≤ √(12420 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12420) ≤ 0.125015941013 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037584564505 + 0.053362752658 * 1.772454 / (2 * (110.830410989042 : ℝ))) * (1 + 0.001215789388) +
        8 / (12420 * 111.445053726040) + 0.125015941013 := by gcongr
    _ ≤ (0.163079200529 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053362752658)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412599489) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284082870578) :
    parallelOracle 12420 0.011 xi bn cd ≤ 0.164096036413 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12420 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12420 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490620394 : ℝ) ≤ plow 12420 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.445053726040 : ℝ) ≤ √(12420 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284082870578 : ℝ) / (2 * 0.560490620394 * 111.445053726040)) * 0.163079200529 +
        0.284082870578 ^ 2 / (2 * 0.560490620394 * 111.445053726040) := by gcongr
    _ ≤ (0.164096036413 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053362752658) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412599489)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284082870578) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12420 12420 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490620394 : ℝ) ≤ plow 12420 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.445053726040 : ℝ) ≤ √(12420 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12420 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12420 Θ 1.22 ≤ 0.011899141826 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.445053726040 := by gcongr <;> linarith
      _ ≤ (0.011899141826 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12420 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12420 12420 0.011 ≤ 0.008577205358 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12420 12420 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12420 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12420 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12420 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12420 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164096036413 + 0.011899141826 + (0.008577205358 : ℝ) *
        (1 + 2 * (0.284082870578 + 0.011899141826) / (0.560490620394 * 111.445053726040))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12420]

end BstLean.Part269.N12420

/-! The original eight local profiles supply actual 12420 moment certificates. -/
namespace BstLean.Part269.N12420
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12420 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12420 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12420 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053362752658 ∧
    0 ≤ bN 12420 BstLean.Part154.csC (groupTheta g) ∧ bN 12420 BstLean.Part154.csC (groupTheta g) ≤ 0.001412599489 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12420 12420 0.011
      (momentAllowance 12420 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12420 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12420 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12420 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12420 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12420 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231003793601 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12420 0.011
      (momentAllowance 12420 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12420 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12420
/-! The actual computed-centre upper energy formula at 12420. -/
namespace BstLean.Part269.N12420
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12420

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12420
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12420)
open BstLean.Part268 (cell12420)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086353717937
  | 2 => 0.087313446027
  | 3 => 0.088273965814
  | 4 => 0.089237292508
  | 5 => 0.090205841502
  | 6 => 0.091182484852
  | 7 => 0.092170612551
  | 8 => 0.093174198540
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12420 12420 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12420 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12420

/-! Actual upper energy certificates on all 43 source endpoints at 12420. -/
namespace BstLean.Part269.N12420
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12420)
open BstLean.Part268 (cell12420)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12420 (gMinus 12420) (1 - (cell12420 i).lower) ≤ 1 ∧
    energyUpper 12420 (gMinus 12420) (BstLean.Part211.gPlus 12420)
      (finiteEnergy 12420 12420 0.011) (1 - (cell12420 i).lower) ≤
      (cell12420 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨10,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨11,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨12,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨13,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨14,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨15,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨16,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨17,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨18,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨19,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨20,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨21,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨22,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨23,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨24,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨25,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨26,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨27,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨28,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨29,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨30,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨31,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨32,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨33,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨34,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨35,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨36,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨37,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨38,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨39,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨40,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨41,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨42,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨43,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨44,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨45,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨46,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨47,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨48,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨49,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨50,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨51,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12420) (by norm_num)
        (q := 1 - (cell12420 ⟨52,by decide⟩).lower)
        (by norm_num [cell12420]) (by norm_num [cell12420])
      exact ⟨E.1,E.2.trans (by norm_num [cell12420])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12420

/-! Source-cell containment and simple scalar guards at 12420. -/
namespace BstLean.Part269.N12420
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12420)
open BstLean.Part268 (cell12420)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12420 ⟨10,by decide⟩).lower ∧ (cell12420 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12420 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12420 ⟨11,by decide⟩).lower ∧ (cell12420 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12420 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12420 ⟨12,by decide⟩).lower ∧ (cell12420 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12420 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12420 ⟨13,by decide⟩).lower ∧ (cell12420 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12420 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12420 ⟨14,by decide⟩).lower ∧ (cell12420 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12420 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12420 ⟨15,by decide⟩).lower ∧ (cell12420 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12420 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12420 ⟨16,by decide⟩).lower ∧ (cell12420 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12420 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12420 ⟨17,by decide⟩).lower ∧ (cell12420 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12420 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12420 ⟨18,by decide⟩).lower ∧ (cell12420 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12420 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12420 ⟨19,by decide⟩).lower ∧ (cell12420 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12420 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12420 ⟨20,by decide⟩).lower ∧ (cell12420 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12420 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12420 ⟨21,by decide⟩).lower ∧ (cell12420 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12420 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12420 ⟨22,by decide⟩).lower ∧ (cell12420 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12420 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12420 ⟨23,by decide⟩).lower ∧ (cell12420 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12420 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12420 ⟨24,by decide⟩).lower ∧ (cell12420 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12420 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12420 ⟨25,by decide⟩).lower ∧ (cell12420 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12420 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12420 ⟨26,by decide⟩).lower ∧ (cell12420 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12420 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12420 ⟨27,by decide⟩).lower ∧ (cell12420 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12420 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12420 ⟨28,by decide⟩).lower ∧ (cell12420 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12420 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12420 ⟨29,by decide⟩).lower ∧ (cell12420 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12420 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12420 ⟨30,by decide⟩).lower ∧ (cell12420 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12420 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12420 ⟨31,by decide⟩).lower ∧ (cell12420 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12420 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12420 ⟨32,by decide⟩).lower ∧ (cell12420 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12420 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12420 ⟨33,by decide⟩).lower ∧ (cell12420 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12420 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12420 ⟨34,by decide⟩).lower ∧ (cell12420 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12420 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12420 ⟨35,by decide⟩).lower ∧ (cell12420 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12420 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12420 ⟨36,by decide⟩).lower ∧ (cell12420 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12420 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12420 ⟨37,by decide⟩).lower ∧ (cell12420 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12420 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12420 ⟨38,by decide⟩).lower ∧ (cell12420 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12420 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12420 ⟨39,by decide⟩).lower ∧ (cell12420 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12420 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12420 ⟨40,by decide⟩).lower ∧ (cell12420 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12420 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12420 ⟨41,by decide⟩).lower ∧ (cell12420 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12420 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12420 ⟨42,by decide⟩).lower ∧ (cell12420 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12420 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12420 ⟨43,by decide⟩).lower ∧ (cell12420 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12420 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12420 ⟨44,by decide⟩).lower ∧ (cell12420 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12420 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12420 ⟨45,by decide⟩).lower ∧ (cell12420 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12420 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12420 ⟨46,by decide⟩).lower ∧ (cell12420 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12420 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12420 ⟨47,by decide⟩).lower ∧ (cell12420 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12420 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12420 ⟨48,by decide⟩).lower ∧ (cell12420 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12420 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12420 ⟨49,by decide⟩).lower ∧ (cell12420 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12420 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12420 ⟨50,by decide⟩).lower ∧ (cell12420 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12420 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12420 ⟨51,by decide⟩).lower ∧ (cell12420 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12420 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12420 ⟨52,by decide⟩).lower ∧ (cell12420 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12420 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12420 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12420 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12420,cell12420,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12420 i).lower ∧
    (cell12420 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12420 i).upper ≤ (0.532 : ℝ) ∧
    (cell12420 i).centre ≤ (0.1 : ℝ) ∧ (cell12420 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12420 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12420 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12420

/-! The local source numeric instances at 12420 have no network premises. -/
namespace BstLean.Part269.N12420
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12420)
open BstLean.Part268 (cell12420)

noncomputable def sourceNumerics12420 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12420 (cell12420 i)
      scalarRow12420.M scalarRow12420.H scalarRow12420.xi := by
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
    energy_allowance := scalarRow12420.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12420]
    centre_nonneg := (scalarRow12420.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12420])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12420
/-! Actual 12421 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12421
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12421 ≤ (1.036212717222 : ℝ) := by
  have hr : (111.449540151586 : ℝ) ≤ √(12421 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.449540151586 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12421 12421 (11 / 1000) ≤
    (0.008576860078 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12421) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.449540151586 : ℝ) ≤ √(12421 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12421)
  have hdiv : K / √(12421 : ℝ) ≤ K / 111.449540151586 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.449540151586 ≤ (0.008576860078 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12421.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12421 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12421 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12421 := gPlus_lower 12421
end BstLean.Part269.N12421

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12421
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036212717221 : ℝ) ≤ wn 12421 := by
  have hn : √(12421 : ℝ) ≤ 111.449540151587 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12421 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.449540151587 ≤ 2 / √(12421 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257638930 : ℝ) ≤ rhoBar 12421 BstLean.Part154.csC ∧
    rhoBar 12421 BstLean.Part154.csC ≤ 0.000257639329 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036212717221 : ℝ) / (1.295212 * 12421) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036212717222 : ℝ) / (1.29521 * 12421) := by gcongr
      _ ≤ (0.000257639329 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12421 BstLean.Part154.csC) ≤ 0.001030623695 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12421 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12421 BstLean.Part154.csC) (piBar (rhoBar 12421 BstLean.Part154.csC)) ≤ 0.000196786867 ∧
    cc1 (rhoBar 12421 BstLean.Part154.csC) (piBar (rhoBar 12421 BstLean.Part154.csC)) ≤ 0.000125216747 ∧
    cc2 (rhoBar 12421 BstLean.Part154.csC) ≤ 0.000072689229 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12421 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12421 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12421 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12421 BstLean.Part154.csC * nuR (rhoBar 12421 BstLean.Part154.csC)) ≤ 0.000515295253 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257639329 : ℝ) * 0.001030623695 := by gcongr
      _ ≤ (0.000515295253 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12421 BstLean.Part154.csC) * nuR (rhoBar 12421 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001030623695 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12421 BstLean.Part154.csC) * rhoBar 12421 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257639329 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257639329 / 2 + 0.399 * 0.001030623695 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196786867 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515295253 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125216747 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257639329 / 1.414213562 := by gcongr
      _ ≤ (0.000072689229 : ℝ) := by norm_num

end BstLean.Part269.N12421

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12421
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12421 BstLean.Part154.csC) (piBar (rhoBar 12421 BstLean.Part154.csC)) ≤ 1.67235E-7 := by
  have hr0 : 0 ≤ rhoBar 12421 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12421 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12421 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12421 BstLean.Part154.csC) (piBar (rhoBar 12421 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12421 BstLean.Part154.csC) (piBar (rhoBar 12421 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12421 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196786867 : ℝ) ^ 2 + 0.000125216747 ^ 2 + 3 * 0.000072689229 ^ 2 +
        2 * 0.797885 * 0.000196786867 * 0.000125216747 + 2 * 0.000196786867 * 0.000072689229 +
        4 * 0.797885 * 0.000125216747 * 0.000072689229 := by gcongr
    _ ≤ (1.67235E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12421 BstLean.Part154.csC Θ ≤ 0.002690447966 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12421 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12421 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12421 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12421 BstLean.Part154.csC) (piBar (rhoBar 12421 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12421 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036212717222 * 1.67235E-7 / (0.000257638930 : ℝ) := by gcongr
    _ ≤ 0.002690447966 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12421 BstLean.Part154.csC Θ ≤ 0.002986358695 + 0.000679831498 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12421 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12421 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12421 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036212717222 : ℝ) * ((2 * Θ * 0.000257639329 +
        (6863 / 10000) * 0.000257639329 * 12421 * 0.001030623695) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002986358695 + 0.000679831498 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12421 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12421 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12421 0.011 Θ ∧ gammaRatio 12421 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12421 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036212717222 : ℝ) * 0.525 / ((1 - 0.011) * 12421) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12421 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12421 0.011 Θ) :=
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
    badAllowance 12421 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12421 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12421 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12421 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12421 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12421 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12421 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12421 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12421 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12421 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12421 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036212717222 : ℝ) * 12421 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12421 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004086358695 + 0.003370279464 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12421

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12421
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12421 BstLean.Part154.csC) (piBar (rhoBar 12421 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12421 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12421 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12421 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12421 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12421 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12421 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12421 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12421 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12421 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12421 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12421 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12421 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12421 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12421 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053076916843 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12421) ≤ 0.010715500302 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12421 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036212717222)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010715500302 + 2 * 0.737676 / 12421) := by gcongr
    _ ≤ (0.053076916843 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12421 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12421

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12421
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490667675 : ℝ) ≤ plow 12421 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12421) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053362355414)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412485183) : eMP 12421 0.011 xi bn ≤ 0.001215691157 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12421 : ℝ) * (1 - 0.011))) ≤ 0.000601022159 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001412485183 / (12421 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000601022159 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000601022159 : ℝ) + 3.141593 * 0.053362355414 / (12421 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001215691157 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053362355414)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412485183) : PiBarMP 12421 12 0.011 xi bn ≤ 0.163072620645 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12421 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037583043823 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.834872671014 : ℝ) ≤ √((12421 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.449540151586 : ℝ) ≤ √(12421 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12421) ≤ 0.125010908469 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037583043823 + 0.053362355414 * 1.772454 / (2 * (110.834872671014 : ℝ))) * (1 + 0.001215691157) +
        8 / (12421 * 111.449540151586) + 0.125010908469 := by gcongr
    _ ≤ (0.163072620645 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053362355414)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412485183) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284079850621) :
    parallelOracle 12421 0.011 xi bn cd ≤ 0.164089382873 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12421 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12421 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490667675 : ℝ) ≤ plow 12421 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.449540151586 : ℝ) ≤ √(12421 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284079850621 : ℝ) / (2 * 0.560490667675 * 111.449540151586)) * 0.163072620645 +
        0.284079850621 ^ 2 / (2 * 0.560490667675 * 111.449540151586) := by gcongr
    _ ≤ (0.164089382873 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053362355414) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412485183)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284079850621) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12421 12421 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490667675 : ℝ) ≤ plow 12421 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.449540151586 : ℝ) ≤ √(12421 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12421 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12421 Θ 1.22 ≤ 0.011898662823 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.449540151586 := by gcongr <;> linarith
      _ ≤ (0.011898662823 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12421 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12421 12421 0.011 ≤ 0.008576860078 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12421 12421 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12421 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12421 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12421 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12421 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164089382873 + 0.011898662823 + (0.008576860078 : ℝ) *
        (1 + 2 * (0.284079850621 + 0.011898662823) / (0.560490667675 * 111.449540151586))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12421]

end BstLean.Part269.N12421

/-! The original eight local profiles supply actual 12421 moment certificates. -/
namespace BstLean.Part269.N12421
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12421 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12421 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12421 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053362355414 ∧
    0 ≤ bN 12421 BstLean.Part154.csC (groupTheta g) ∧ bN 12421 BstLean.Part154.csC (groupTheta g) ≤ 0.001412485183 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12421 12421 0.011
      (momentAllowance 12421 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12421 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12421 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12421 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12421 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12421 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231002933778 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12421 0.011
      (momentAllowance 12421 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12421 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12421
/-! The actual computed-centre upper energy formula at 12421. -/
namespace BstLean.Part269.N12421
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12421

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12421
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12421)
open BstLean.Part268 (cell12421)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086350450120
  | 2 => 0.087310109628
  | 3 => 0.088270549504
  | 4 => 0.089233782459
  | 5 => 0.090202220960
  | 6 => 0.091178733671
  | 7 => 0.092166706669
  | 8 => 0.093170109402
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12421 12421 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12421 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12421

/-! Actual upper energy certificates on all 43 source endpoints at 12421. -/
namespace BstLean.Part269.N12421
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12421)
open BstLean.Part268 (cell12421)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12421 (gMinus 12421) (1 - (cell12421 i).lower) ≤ 1 ∧
    energyUpper 12421 (gMinus 12421) (BstLean.Part211.gPlus 12421)
      (finiteEnergy 12421 12421 0.011) (1 - (cell12421 i).lower) ≤
      (cell12421 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨10,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨11,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨12,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨13,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨14,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨15,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨16,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨17,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨18,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨19,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨20,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨21,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨22,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨23,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨24,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨25,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨26,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨27,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨28,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨29,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨30,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨31,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨32,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨33,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨34,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨35,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨36,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨37,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨38,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨39,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨40,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨41,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨42,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨43,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨44,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨45,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨46,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨47,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨48,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨49,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨50,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨51,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12421) (by norm_num)
        (q := 1 - (cell12421 ⟨52,by decide⟩).lower)
        (by norm_num [cell12421]) (by norm_num [cell12421])
      exact ⟨E.1,E.2.trans (by norm_num [cell12421])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12421

/-! Source-cell containment and simple scalar guards at 12421. -/
namespace BstLean.Part269.N12421
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12421)
open BstLean.Part268 (cell12421)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12421 ⟨10,by decide⟩).lower ∧ (cell12421 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12421 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12421 ⟨11,by decide⟩).lower ∧ (cell12421 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12421 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12421 ⟨12,by decide⟩).lower ∧ (cell12421 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12421 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12421 ⟨13,by decide⟩).lower ∧ (cell12421 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12421 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12421 ⟨14,by decide⟩).lower ∧ (cell12421 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12421 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12421 ⟨15,by decide⟩).lower ∧ (cell12421 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12421 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12421 ⟨16,by decide⟩).lower ∧ (cell12421 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12421 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12421 ⟨17,by decide⟩).lower ∧ (cell12421 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12421 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12421 ⟨18,by decide⟩).lower ∧ (cell12421 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12421 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12421 ⟨19,by decide⟩).lower ∧ (cell12421 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12421 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12421 ⟨20,by decide⟩).lower ∧ (cell12421 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12421 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12421 ⟨21,by decide⟩).lower ∧ (cell12421 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12421 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12421 ⟨22,by decide⟩).lower ∧ (cell12421 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12421 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12421 ⟨23,by decide⟩).lower ∧ (cell12421 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12421 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12421 ⟨24,by decide⟩).lower ∧ (cell12421 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12421 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12421 ⟨25,by decide⟩).lower ∧ (cell12421 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12421 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12421 ⟨26,by decide⟩).lower ∧ (cell12421 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12421 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12421 ⟨27,by decide⟩).lower ∧ (cell12421 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12421 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12421 ⟨28,by decide⟩).lower ∧ (cell12421 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12421 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12421 ⟨29,by decide⟩).lower ∧ (cell12421 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12421 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12421 ⟨30,by decide⟩).lower ∧ (cell12421 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12421 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12421 ⟨31,by decide⟩).lower ∧ (cell12421 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12421 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12421 ⟨32,by decide⟩).lower ∧ (cell12421 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12421 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12421 ⟨33,by decide⟩).lower ∧ (cell12421 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12421 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12421 ⟨34,by decide⟩).lower ∧ (cell12421 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12421 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12421 ⟨35,by decide⟩).lower ∧ (cell12421 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12421 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12421 ⟨36,by decide⟩).lower ∧ (cell12421 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12421 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12421 ⟨37,by decide⟩).lower ∧ (cell12421 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12421 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12421 ⟨38,by decide⟩).lower ∧ (cell12421 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12421 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12421 ⟨39,by decide⟩).lower ∧ (cell12421 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12421 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12421 ⟨40,by decide⟩).lower ∧ (cell12421 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12421 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12421 ⟨41,by decide⟩).lower ∧ (cell12421 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12421 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12421 ⟨42,by decide⟩).lower ∧ (cell12421 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12421 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12421 ⟨43,by decide⟩).lower ∧ (cell12421 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12421 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12421 ⟨44,by decide⟩).lower ∧ (cell12421 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12421 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12421 ⟨45,by decide⟩).lower ∧ (cell12421 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12421 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12421 ⟨46,by decide⟩).lower ∧ (cell12421 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12421 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12421 ⟨47,by decide⟩).lower ∧ (cell12421 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12421 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12421 ⟨48,by decide⟩).lower ∧ (cell12421 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12421 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12421 ⟨49,by decide⟩).lower ∧ (cell12421 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12421 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12421 ⟨50,by decide⟩).lower ∧ (cell12421 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12421 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12421 ⟨51,by decide⟩).lower ∧ (cell12421 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12421 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12421 ⟨52,by decide⟩).lower ∧ (cell12421 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12421 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12421 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12421 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12421,cell12421,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12421 i).lower ∧
    (cell12421 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12421 i).upper ≤ (0.532 : ℝ) ∧
    (cell12421 i).centre ≤ (0.1 : ℝ) ∧ (cell12421 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12421 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12421 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12421

/-! The local source numeric instances at 12421 have no network premises. -/
namespace BstLean.Part269.N12421
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12421)
open BstLean.Part268 (cell12421)

noncomputable def sourceNumerics12421 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12421 (cell12421 i)
      scalarRow12421.M scalarRow12421.H scalarRow12421.xi := by
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
    energy_allowance := scalarRow12421.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12421]
    centre_nonneg := (scalarRow12421.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12421])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12421
/-! Actual 12422 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12422
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12422 ≤ (1.036211246626 : ℝ) := by
  have hr : (111.454026396537 : ℝ) ≤ √(12422 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.454026396537 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12422 12422 (11 / 1000) ≤
    (0.008576514840 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12422) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.454026396537 : ℝ) ≤ √(12422 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12422)
  have hdiv : K / √(12422 : ℝ) ≤ K / 111.454026396537 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.454026396537 ≤ (0.008576514840 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12422.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12422 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12422 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12422 := gPlus_lower 12422
end BstLean.Part269.N12422

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12422
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036211246625 : ℝ) ≤ wn 12422 := by
  have hn : √(12422 : ℝ) ≤ 111.454026396538 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12422 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.454026396538 ≤ 2 / √(12422 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257617824 : ℝ) ≤ rhoBar 12422 BstLean.Part154.csC ∧
    rhoBar 12422 BstLean.Part154.csC ≤ 0.000257618223 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036211246625 : ℝ) / (1.295212 * 12422) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036211246626 : ℝ) / (1.29521 * 12422) := by gcongr
      _ ≤ (0.000257618223 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12422 BstLean.Part154.csC) ≤ 0.001030539260 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12422 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12422 BstLean.Part154.csC) (piBar (rhoBar 12422 BstLean.Part154.csC)) ≤ 0.000196770745 ∧
    cc1 (rhoBar 12422 BstLean.Part154.csC) (piBar (rhoBar 12422 BstLean.Part154.csC)) ≤ 0.000125206489 ∧
    cc2 (rhoBar 12422 BstLean.Part154.csC) ≤ 0.000072683274 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12422 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12422 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12422 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12422 BstLean.Part154.csC * nuR (rhoBar 12422 BstLean.Part154.csC)) ≤ 0.000515253038 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257618223 : ℝ) * 0.001030539260 := by gcongr
      _ ≤ (0.000515253038 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12422 BstLean.Part154.csC) * nuR (rhoBar 12422 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001030539260 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12422 BstLean.Part154.csC) * rhoBar 12422 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257618223 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257618223 / 2 + 0.399 * 0.001030539260 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196770745 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515253038 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125206489 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257618223 / 1.414213562 := by gcongr
      _ ≤ (0.000072683274 : ℝ) := by norm_num

end BstLean.Part269.N12422

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12422
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12422 BstLean.Part154.csC) (piBar (rhoBar 12422 BstLean.Part154.csC)) ≤ 1.67208E-7 := by
  have hr0 : 0 ≤ rhoBar 12422 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12422 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12422 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12422 BstLean.Part154.csC) (piBar (rhoBar 12422 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12422 BstLean.Part154.csC) (piBar (rhoBar 12422 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12422 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196770745 : ℝ) ^ 2 + 0.000125206489 ^ 2 + 3 * 0.000072683274 ^ 2 +
        2 * 0.797885 * 0.000196770745 * 0.000125206489 + 2 * 0.000196770745 * 0.000072683274 +
        4 * 0.797885 * 0.000125206489 * 0.000072683274 := by gcongr
    _ ≤ (1.67208E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12422 BstLean.Part154.csC Θ ≤ 0.002690230163 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12422 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12422 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12422 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12422 BstLean.Part154.csC) (piBar (rhoBar 12422 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12422 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036211246626 * 1.67208E-7 / (0.000257617824 : ℝ) := by gcongr
    _ ≤ 0.002690230163 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12422 BstLean.Part154.csC Θ ≤ 0.002986105561 + 0.000679774841 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12422 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12422 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12422 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036211246626 : ℝ) * ((2 * Θ * 0.000257618223 +
        (6863 / 10000) * 0.000257618223 * 12422 * 0.001030539260) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002986105561 + 0.000679774841 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12422 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12422 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12422 0.011 Θ ∧ gammaRatio 12422 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12422 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036211246626 : ℝ) * 0.525 / ((1 - 0.011) * 12422) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12422 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12422 0.011 Θ) :=
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
    badAllowance 12422 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12422 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12422 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12422 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12422 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12422 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12422 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12422 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12422 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12422 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12422 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036211246626 : ℝ) * 12422 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12422 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004086105561 + 0.003370005004 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12422

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12422
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12422 BstLean.Part154.csC) (piBar (rhoBar 12422 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12422 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12422 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12422 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12422 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12422 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12422 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12422 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12422 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12422 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12422 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12422 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12422 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12422 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12422 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053074756971 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12422) ≤ 0.010715068982 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12422 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036211246626)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010715068982 + 2 * 0.737676 / 12422) := by gcongr
    _ ≤ (0.053074756971 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12422 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12422

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12422
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490714949 : ℝ) ≤ plow 12422 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12422) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053361958189)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412370836) : eMP 12422 0.011 xi bn ≤ 0.001215592919 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12422 : ℝ) * (1 - 0.011))) ≤ 0.000600973640 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001412370836 / (12422 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600973640 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600973640 : ℝ) + 3.141593 * 0.053361958189 / (12422 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001215592919 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053361958189)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412370836) : PiBarMP 12422 12 0.011 xi bn ≤ 0.163066040764 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12422 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037581522535 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.839334173388 : ℝ) ≤ √((12422 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.454026396537 : ℝ) ≤ √(12422 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12422) ≤ 0.125005876533 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037581522535 + 0.053361958189 * 1.772454 / (2 * (110.839334173388 : ℝ))) * (1 + 0.001215592919) +
        8 / (12422 * 111.454026396537) + 0.125005876533 := by gcongr
    _ ≤ (0.163066040764 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053361958189)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412370836) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284076830964) :
    parallelOracle 12422 0.011 xi bn cd ≤ 0.164082729345 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12422 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12422 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490714949 : ℝ) ≤ plow 12422 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.454026396537 : ℝ) ≤ √(12422 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284076830964 : ℝ) / (2 * 0.560490714949 * 111.454026396537)) * 0.163066040764 +
        0.284076830964 ^ 2 / (2 * 0.560490714949 * 111.454026396537) := by gcongr
    _ ≤ (0.164082729345 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053361958189) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412370836)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284076830964) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12422 12422 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490714949 : ℝ) ≤ plow 12422 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.454026396537 : ℝ) ≤ √(12422 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12422 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12422 Θ 1.22 ≤ 0.011898183878 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.454026396537 := by gcongr <;> linarith
      _ ≤ (0.011898183878 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12422 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12422 12422 0.011 ≤ 0.008576514840 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12422 12422 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12422 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12422 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12422 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12422 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164082729345 + 0.011898183878 + (0.008576514840 : ℝ) *
        (1 + 2 * (0.284076830964 + 0.011898183878) / (0.560490714949 * 111.454026396537))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12422]

end BstLean.Part269.N12422

/-! The original eight local profiles supply actual 12422 moment certificates. -/
namespace BstLean.Part269.N12422
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12422 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12422 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12422 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053361958189 ∧
    0 ≤ bN 12422 BstLean.Part154.csC (groupTheta g) ∧ bN 12422 BstLean.Part154.csC (groupTheta g) ≤ 0.001412370836 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12422 12422 0.011
      (momentAllowance 12422 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12422 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12422 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12422 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12422 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12422 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231002073993 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12422 0.011
      (momentAllowance 12422 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12422 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12422
/-! The actual computed-centre upper energy formula at 12422. -/
namespace BstLean.Part269.N12422
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12422

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12422
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12422)
open BstLean.Part268 (cell12422)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086347183756
  | 2 => 0.087306774747
  | 3 => 0.088267134791
  | 4 => 0.089230274102
  | 5 => 0.090198602230
  | 6 => 0.091174984445
  | 7 => 0.092162802914
  | 8 => 0.093166022597
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12422 12422 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12422 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12422

/-! Actual upper energy certificates on all 43 source endpoints at 12422. -/
namespace BstLean.Part269.N12422
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12422)
open BstLean.Part268 (cell12422)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12422 (gMinus 12422) (1 - (cell12422 i).lower) ≤ 1 ∧
    energyUpper 12422 (gMinus 12422) (BstLean.Part211.gPlus 12422)
      (finiteEnergy 12422 12422 0.011) (1 - (cell12422 i).lower) ≤
      (cell12422 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨10,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨11,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨12,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨13,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨14,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨15,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨16,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨17,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨18,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨19,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨20,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨21,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨22,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨23,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨24,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨25,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨26,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨27,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨28,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨29,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨30,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨31,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨32,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨33,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨34,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨35,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨36,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨37,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨38,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨39,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨40,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨41,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨42,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨43,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨44,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨45,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨46,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨47,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨48,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨49,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨50,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨51,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12422) (by norm_num)
        (q := 1 - (cell12422 ⟨52,by decide⟩).lower)
        (by norm_num [cell12422]) (by norm_num [cell12422])
      exact ⟨E.1,E.2.trans (by norm_num [cell12422])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12422

/-! Source-cell containment and simple scalar guards at 12422. -/
namespace BstLean.Part269.N12422
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12422)
open BstLean.Part268 (cell12422)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12422 ⟨10,by decide⟩).lower ∧ (cell12422 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12422 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12422 ⟨11,by decide⟩).lower ∧ (cell12422 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12422 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12422 ⟨12,by decide⟩).lower ∧ (cell12422 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12422 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12422 ⟨13,by decide⟩).lower ∧ (cell12422 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12422 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12422 ⟨14,by decide⟩).lower ∧ (cell12422 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12422 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12422 ⟨15,by decide⟩).lower ∧ (cell12422 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12422 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12422 ⟨16,by decide⟩).lower ∧ (cell12422 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12422 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12422 ⟨17,by decide⟩).lower ∧ (cell12422 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12422 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12422 ⟨18,by decide⟩).lower ∧ (cell12422 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12422 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12422 ⟨19,by decide⟩).lower ∧ (cell12422 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12422 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12422 ⟨20,by decide⟩).lower ∧ (cell12422 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12422 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12422 ⟨21,by decide⟩).lower ∧ (cell12422 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12422 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12422 ⟨22,by decide⟩).lower ∧ (cell12422 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12422 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12422 ⟨23,by decide⟩).lower ∧ (cell12422 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12422 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12422 ⟨24,by decide⟩).lower ∧ (cell12422 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12422 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12422 ⟨25,by decide⟩).lower ∧ (cell12422 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12422 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12422 ⟨26,by decide⟩).lower ∧ (cell12422 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12422 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12422 ⟨27,by decide⟩).lower ∧ (cell12422 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12422 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12422 ⟨28,by decide⟩).lower ∧ (cell12422 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12422 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12422 ⟨29,by decide⟩).lower ∧ (cell12422 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12422 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12422 ⟨30,by decide⟩).lower ∧ (cell12422 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12422 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12422 ⟨31,by decide⟩).lower ∧ (cell12422 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12422 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12422 ⟨32,by decide⟩).lower ∧ (cell12422 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12422 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12422 ⟨33,by decide⟩).lower ∧ (cell12422 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12422 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12422 ⟨34,by decide⟩).lower ∧ (cell12422 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12422 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12422 ⟨35,by decide⟩).lower ∧ (cell12422 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12422 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12422 ⟨36,by decide⟩).lower ∧ (cell12422 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12422 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12422 ⟨37,by decide⟩).lower ∧ (cell12422 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12422 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12422 ⟨38,by decide⟩).lower ∧ (cell12422 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12422 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12422 ⟨39,by decide⟩).lower ∧ (cell12422 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12422 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12422 ⟨40,by decide⟩).lower ∧ (cell12422 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12422 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12422 ⟨41,by decide⟩).lower ∧ (cell12422 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12422 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12422 ⟨42,by decide⟩).lower ∧ (cell12422 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12422 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12422 ⟨43,by decide⟩).lower ∧ (cell12422 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12422 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12422 ⟨44,by decide⟩).lower ∧ (cell12422 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12422 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12422 ⟨45,by decide⟩).lower ∧ (cell12422 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12422 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12422 ⟨46,by decide⟩).lower ∧ (cell12422 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12422 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12422 ⟨47,by decide⟩).lower ∧ (cell12422 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12422 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12422 ⟨48,by decide⟩).lower ∧ (cell12422 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12422 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12422 ⟨49,by decide⟩).lower ∧ (cell12422 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12422 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12422 ⟨50,by decide⟩).lower ∧ (cell12422 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12422 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12422 ⟨51,by decide⟩).lower ∧ (cell12422 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12422 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12422 ⟨52,by decide⟩).lower ∧ (cell12422 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12422 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12422 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12422 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12422,cell12422,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12422 i).lower ∧
    (cell12422 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12422 i).upper ≤ (0.532 : ℝ) ∧
    (cell12422 i).centre ≤ (0.1 : ℝ) ∧ (cell12422 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12422 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12422 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12422

/-! The local source numeric instances at 12422 have no network premises. -/
namespace BstLean.Part269.N12422
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12422)
open BstLean.Part268 (cell12422)

noncomputable def sourceNumerics12422 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12422 (cell12422 i)
      scalarRow12422.M scalarRow12422.H scalarRow12422.xi := by
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
    energy_allowance := scalarRow12422.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12422]
    centre_nonneg := (scalarRow12422.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12422])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12422
/-! Actual 12423 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12423
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12423 ≤ (1.036209776209 : ℝ) := by
  have hr : (111.458512460915 : ℝ) ≤ √(12423 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.458512460915 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12423 12423 (11 / 1000) ≤
    (0.008576169643 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12423) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.458512460915 : ℝ) ≤ √(12423 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12423)
  have hdiv : K / √(12423 : ℝ) ≤ K / 111.458512460915 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.458512460915 ≤ (0.008576169643 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12423.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12423 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12423 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12423 := gPlus_lower 12423
end BstLean.Part269.N12423

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12423
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036209776208 : ℝ) ≤ wn 12423 := by
  have hn : √(12423 : ℝ) ≤ 111.458512460916 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12423 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.458512460916 ≤ 2 / √(12423 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257596721 : ℝ) ≤ rhoBar 12423 BstLean.Part154.csC ∧
    rhoBar 12423 BstLean.Part154.csC ≤ 0.000257597120 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036209776208 : ℝ) / (1.295212 * 12423) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036209776209 : ℝ) / (1.29521 * 12423) := by gcongr
      _ ≤ (0.000257597120 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12423 BstLean.Part154.csC) ≤ 0.001030454837 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12423 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12423 BstLean.Part154.csC) (piBar (rhoBar 12423 BstLean.Part154.csC)) ≤ 0.000196754626 ∧
    cc1 (rhoBar 12423 BstLean.Part154.csC) (piBar (rhoBar 12423 BstLean.Part154.csC)) ≤ 0.000125196232 ∧
    cc2 (rhoBar 12423 BstLean.Part154.csC) ≤ 0.000072677320 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12423 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12423 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12423 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12423 BstLean.Part154.csC * nuR (rhoBar 12423 BstLean.Part154.csC)) ≤ 0.000515210829 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257597120 : ℝ) * 0.001030454837 := by gcongr
      _ ≤ (0.000515210829 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12423 BstLean.Part154.csC) * nuR (rhoBar 12423 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001030454837 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12423 BstLean.Part154.csC) * rhoBar 12423 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257597120 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257597120 / 2 + 0.399 * 0.001030454837 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196754626 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515210829 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125196232 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257597120 / 1.414213562 := by gcongr
      _ ≤ (0.000072677320 : ℝ) := by norm_num

end BstLean.Part269.N12423

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12423
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12423 BstLean.Part154.csC) (piBar (rhoBar 12423 BstLean.Part154.csC)) ≤ 1.67180E-7 := by
  have hr0 : 0 ≤ rhoBar 12423 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12423 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12423 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12423 BstLean.Part154.csC) (piBar (rhoBar 12423 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12423 BstLean.Part154.csC) (piBar (rhoBar 12423 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12423 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196754626 : ℝ) ^ 2 + 0.000125196232 ^ 2 + 3 * 0.000072677320 ^ 2 +
        2 * 0.797885 * 0.000196754626 * 0.000125196232 + 2 * 0.000196754626 * 0.000072677320 +
        4 * 0.797885 * 0.000125196232 * 0.000072677320 := by gcongr
    _ ≤ (1.67180E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12423 BstLean.Part154.csC Θ ≤ 0.002689996204 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12423 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12423 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12423 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12423 BstLean.Part154.csC) (piBar (rhoBar 12423 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12423 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036209776209 * 1.67180E-7 / (0.000257596721 : ℝ) := by gcongr
    _ ≤ 0.002689996204 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12423 BstLean.Part154.csC Θ ≤ 0.002985852459 + 0.000679718192 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12423 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12423 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12423 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036209776209 : ℝ) * ((2 * Θ * 0.000257597120 +
        (6863 / 10000) * 0.000257597120 * 12423 * 0.001030454837) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002985852459 + 0.000679718192 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12423 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12423 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12423 0.011 Θ ∧ gammaRatio 12423 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12423 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036209776209 : ℝ) * 0.525 / ((1 - 0.011) * 12423) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12423 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12423 0.011 Θ) :=
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
    badAllowance 12423 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12423 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12423 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12423 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12423 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12423 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12423 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12423 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12423 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12423 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12423 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036209776209 : ℝ) * 12423 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12423 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004085852459 + 0.003369714396 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12423

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12423
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12423 BstLean.Part154.csC) (piBar (rhoBar 12423 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12423 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12423 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12423 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12423 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12423 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12423 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12423 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12423 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12423 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12423 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12423 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12423 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12423 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12423 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053072597361 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12423) ≤ 0.010714637714 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12423 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036209776209)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010714637714 + 2 * 0.737676 / 12423) := by gcongr
    _ ≤ (0.053072597361 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12423 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12423

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12423
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490762215 : ℝ) ≤ plow 12423 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12423) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053361552517)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412248008) : eMP 12423 0.011 xi bn ≤ 0.001215491077 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12423 : ℝ) * (1 - 0.011))) ≤ 0.000600923320 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001412248008 / (12423 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600923320 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600923320 : ℝ) + 3.141593 * 0.053361552517 / (12423 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001215491077 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053361552517)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412248008) : PiBarMP 12423 12 0.011 xi bn ≤ 0.163059348250 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12423 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037579888345 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.843795496184 : ℝ) ≤ √((12423 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.458512460915 : ℝ) ≤ √(12423 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12423) ≤ 0.125000845204 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037579888345 + 0.053361552517 * 1.772454 / (2 * (110.843795496184 : ℝ))) * (1 + 0.001215491077) +
        8 / (12423 * 111.458512460915) + 0.125000845204 := by gcongr
    _ ≤ (0.163059348250 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053361552517)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412248008) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284073793283) :
    parallelOracle 12423 0.011 xi bn cd ≤ 0.164075962831 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12423 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12423 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490762215 : ℝ) ≤ plow 12423 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.458512460915 : ℝ) ≤ √(12423 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284073793283 : ℝ) / (2 * 0.560490762215 * 111.458512460915)) * 0.163059348250 +
        0.284073793283 ^ 2 / (2 * 0.560490762215 * 111.458512460915) := by gcongr
    _ ≤ (0.164075962831 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053361552517) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412248008)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284073793283) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12423 12423 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490762215 : ℝ) ≤ plow 12423 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.458512460915 : ℝ) ≤ √(12423 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12423 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12423 Θ 1.22 ≤ 0.011897704992 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.458512460915 := by gcongr <;> linarith
      _ ≤ (0.011897704992 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12423 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12423 12423 0.011 ≤ 0.008576169643 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12423 12423 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12423 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12423 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12423 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12423 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164075962831 + 0.011897704992 + (0.008576169643 : ℝ) *
        (1 + 2 * (0.284073793283 + 0.011897704992) / (0.560490762215 * 111.458512460915))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12423]

end BstLean.Part269.N12423

/-! The original eight local profiles supply actual 12423 moment certificates. -/
namespace BstLean.Part269.N12423
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12423 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12423 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12423 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053361552517 ∧
    0 ≤ bN 12423 BstLean.Part154.csC (groupTheta g) ∧ bN 12423 BstLean.Part154.csC (groupTheta g) ≤ 0.001412248008 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12423 12423 0.011
      (momentAllowance 12423 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12423 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12423 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12423 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12423 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12423 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231001195922 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12423 0.011
      (momentAllowance 12423 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12423 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12423
/-! The actual computed-centre upper energy formula at 12423. -/
namespace BstLean.Part269.N12423
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12423

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12423
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12423)
open BstLean.Part268 (cell12423)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086343918844
  | 2 => 0.087303441381
  | 3 => 0.088263721672
  | 4 => 0.089226767437
  | 5 => 0.090194985308
  | 6 => 0.091171237170
  | 7 => 0.092158901282
  | 8 => 0.093161938121
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12423 12423 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12423 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12423

/-! Actual upper energy certificates on all 43 source endpoints at 12423. -/
namespace BstLean.Part269.N12423
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12423)
open BstLean.Part268 (cell12423)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12423 (gMinus 12423) (1 - (cell12423 i).lower) ≤ 1 ∧
    energyUpper 12423 (gMinus 12423) (BstLean.Part211.gPlus 12423)
      (finiteEnergy 12423 12423 0.011) (1 - (cell12423 i).lower) ≤
      (cell12423 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨10,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨11,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨12,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨13,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨14,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨15,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨16,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨17,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨18,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨19,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨20,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨21,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨22,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨23,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨24,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨25,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨26,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨27,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨28,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨29,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨30,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨31,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨32,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨33,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨34,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨35,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨36,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨37,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨38,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨39,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨40,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨41,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨42,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨43,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨44,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨45,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨46,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨47,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨48,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨49,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨50,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨51,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12423) (by norm_num)
        (q := 1 - (cell12423 ⟨52,by decide⟩).lower)
        (by norm_num [cell12423]) (by norm_num [cell12423])
      exact ⟨E.1,E.2.trans (by norm_num [cell12423])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12423

/-! Source-cell containment and simple scalar guards at 12423. -/
namespace BstLean.Part269.N12423
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12423)
open BstLean.Part268 (cell12423)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12423 ⟨10,by decide⟩).lower ∧ (cell12423 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12423 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12423 ⟨11,by decide⟩).lower ∧ (cell12423 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12423 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12423 ⟨12,by decide⟩).lower ∧ (cell12423 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12423 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12423 ⟨13,by decide⟩).lower ∧ (cell12423 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12423 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12423 ⟨14,by decide⟩).lower ∧ (cell12423 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12423 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12423 ⟨15,by decide⟩).lower ∧ (cell12423 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12423 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12423 ⟨16,by decide⟩).lower ∧ (cell12423 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12423 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12423 ⟨17,by decide⟩).lower ∧ (cell12423 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12423 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12423 ⟨18,by decide⟩).lower ∧ (cell12423 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12423 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12423 ⟨19,by decide⟩).lower ∧ (cell12423 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12423 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12423 ⟨20,by decide⟩).lower ∧ (cell12423 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12423 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12423 ⟨21,by decide⟩).lower ∧ (cell12423 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12423 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12423 ⟨22,by decide⟩).lower ∧ (cell12423 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12423 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12423 ⟨23,by decide⟩).lower ∧ (cell12423 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12423 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12423 ⟨24,by decide⟩).lower ∧ (cell12423 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12423 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12423 ⟨25,by decide⟩).lower ∧ (cell12423 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12423 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12423 ⟨26,by decide⟩).lower ∧ (cell12423 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12423 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12423 ⟨27,by decide⟩).lower ∧ (cell12423 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12423 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12423 ⟨28,by decide⟩).lower ∧ (cell12423 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12423 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12423 ⟨29,by decide⟩).lower ∧ (cell12423 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12423 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12423 ⟨30,by decide⟩).lower ∧ (cell12423 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12423 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12423 ⟨31,by decide⟩).lower ∧ (cell12423 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12423 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12423 ⟨32,by decide⟩).lower ∧ (cell12423 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12423 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12423 ⟨33,by decide⟩).lower ∧ (cell12423 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12423 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12423 ⟨34,by decide⟩).lower ∧ (cell12423 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12423 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12423 ⟨35,by decide⟩).lower ∧ (cell12423 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12423 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12423 ⟨36,by decide⟩).lower ∧ (cell12423 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12423 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12423 ⟨37,by decide⟩).lower ∧ (cell12423 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12423 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12423 ⟨38,by decide⟩).lower ∧ (cell12423 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12423 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12423 ⟨39,by decide⟩).lower ∧ (cell12423 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12423 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12423 ⟨40,by decide⟩).lower ∧ (cell12423 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12423 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12423 ⟨41,by decide⟩).lower ∧ (cell12423 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12423 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12423 ⟨42,by decide⟩).lower ∧ (cell12423 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12423 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12423 ⟨43,by decide⟩).lower ∧ (cell12423 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12423 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12423 ⟨44,by decide⟩).lower ∧ (cell12423 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12423 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12423 ⟨45,by decide⟩).lower ∧ (cell12423 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12423 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12423 ⟨46,by decide⟩).lower ∧ (cell12423 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12423 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12423 ⟨47,by decide⟩).lower ∧ (cell12423 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12423 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12423 ⟨48,by decide⟩).lower ∧ (cell12423 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12423 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12423 ⟨49,by decide⟩).lower ∧ (cell12423 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12423 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12423 ⟨50,by decide⟩).lower ∧ (cell12423 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12423 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12423 ⟨51,by decide⟩).lower ∧ (cell12423 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12423 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12423 ⟨52,by decide⟩).lower ∧ (cell12423 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12423 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12423 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12423 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12423,cell12423,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12423 i).lower ∧
    (cell12423 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12423 i).upper ≤ (0.532 : ℝ) ∧
    (cell12423 i).centre ≤ (0.1 : ℝ) ∧ (cell12423 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12423 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12423 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12423

/-! The local source numeric instances at 12423 have no network premises. -/
namespace BstLean.Part269.N12423
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12423)
open BstLean.Part268 (cell12423)

noncomputable def sourceNumerics12423 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12423 (cell12423 i)
      scalarRow12423.M scalarRow12423.H scalarRow12423.xi := by
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
    energy_allowance := scalarRow12423.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12423]
    centre_nonneg := (scalarRow12423.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12423])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12423
/-! Actual 12424 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12424
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12424 ≤ (1.036208305971 : ℝ) := by
  have hr : (111.462998344742 : ℝ) ≤ √(12424 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.462998344742 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12424 12424 (11 / 1000) ≤
    (0.008575824488 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12424) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.462998344742 : ℝ) ≤ √(12424 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12424)
  have hdiv : K / √(12424 : ℝ) ≤ K / 111.462998344742 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.462998344742 ≤ (0.008575824488 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12424.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12424 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12424 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12424 := gPlus_lower 12424
end BstLean.Part269.N12424

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12424
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036208305970 : ℝ) ≤ wn 12424 := by
  have hn : √(12424 : ℝ) ≤ 111.462998344743 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12424 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.462998344743 ≤ 2 / √(12424 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000257575622 : ℝ) ≤ rhoBar 12424 BstLean.Part154.csC ∧
    rhoBar 12424 BstLean.Part154.csC ≤ 0.000257576021 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036208305970 : ℝ) / (1.295212 * 12424) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036208305971 : ℝ) / (1.29521 * 12424) := by gcongr
      _ ≤ (0.000257576021 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12424 BstLean.Part154.csC) ≤ 0.001030370430 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12424 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12424 BstLean.Part154.csC) (piBar (rhoBar 12424 BstLean.Part154.csC)) ≤ 0.000196738509 ∧
    cc1 (rhoBar 12424 BstLean.Part154.csC) (piBar (rhoBar 12424 BstLean.Part154.csC)) ≤ 0.000125185977 ∧
    cc2 (rhoBar 12424 BstLean.Part154.csC) ≤ 0.000072671367 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12424 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12424 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12424 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12424 BstLean.Part154.csC * nuR (rhoBar 12424 BstLean.Part154.csC)) ≤ 0.000515168629 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000257576021 : ℝ) * 0.001030370430 := by gcongr
      _ ≤ (0.000515168629 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12424 BstLean.Part154.csC) * nuR (rhoBar 12424 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001030370430 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12424 BstLean.Part154.csC) * rhoBar 12424 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000257576021 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000257576021 / 2 + 0.399 * 0.001030370430 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000196738509 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000515168629 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125185977 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000257576021 / 1.414213562 := by gcongr
      _ ≤ (0.000072671367 : ℝ) := by norm_num

end BstLean.Part269.N12424

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12424
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12424 BstLean.Part154.csC) (piBar (rhoBar 12424 BstLean.Part154.csC)) ≤ 1.67153E-7 := by
  have hr0 : 0 ≤ rhoBar 12424 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12424 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12424 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12424 BstLean.Part154.csC) (piBar (rhoBar 12424 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12424 BstLean.Part154.csC) (piBar (rhoBar 12424 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12424 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000196738509 : ℝ) ^ 2 + 0.000125185977 ^ 2 + 3 * 0.000072671367 ^ 2 +
        2 * 0.797885 * 0.000196738509 * 0.000125185977 + 2 * 0.000196738509 * 0.000072671367 +
        4 * 0.797885 * 0.000125185977 * 0.000072671367 := by gcongr
    _ ≤ (1.67153E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12424 BstLean.Part154.csC Θ ≤ 0.002689778259 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12424 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12424 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12424 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12424 BstLean.Part154.csC) (piBar (rhoBar 12424 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12424 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036208305971 * 1.67153E-7 / (0.000257575622 : ℝ) := by gcongr
    _ ≤ 0.002689778259 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12424 BstLean.Part154.csC Θ ≤ 0.002985599411 + 0.000679661554 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12424 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12424 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12424 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036208305971 : ℝ) * ((2 * Θ * 0.000257576021 +
        (6863 / 10000) * 0.000257576021 * 12424 * 0.001030370430) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002985599411 + 0.000679661554 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12424 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12424 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12424 0.011 Θ ∧ gammaRatio 12424 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12424 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036208305971 : ℝ) * 0.525 / ((1 - 0.011) * 12424) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12424 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12424 0.011 Θ) :=
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
    badAllowance 12424 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12424 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12424 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12424 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12424 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12424 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12424 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12424 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12424 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12424 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12424 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036208305971 : ℝ) * 12424 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12424 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004085599411 + 0.003369439813 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12424

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12424
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12424 BstLean.Part154.csC) (piBar (rhoBar 12424 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12424 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12424 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12424 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12424 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12424 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12424 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12424 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12424 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12424 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12424 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12424 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12424 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12424 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12424 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053070438014 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12424) ≤ 0.010714206498 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12424 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036208305971)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010714206498 + 2 * 0.737676 / 12424) := by gcongr
    _ ≤ (0.053070438014 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12424 12 ≤ 0.0015 := by
  exact BstLean.Part269.S2.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12424

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12424
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560490809473 : ℝ) ≤ plow 12424 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12424) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053361155313)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412133586) : eMP 12424 0.011 xi bn ≤ 0.001215392821 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12424 : ℝ) * (1 - 0.011))) ≤ 0.000600874792 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001412133586 / (12424 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000600874792 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000600874792 : ℝ) + 3.141593 * 0.053361155313 / (12424 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001215392821 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053361155313)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412133586) : PiBarMP 12424 12 0.011 xi bn ≤ 0.163052768462 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12424 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037578365931 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.848256639425 : ℝ) ≤ √((12424 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.462998344742 : ℝ) ≤ √(12424 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12424) ≤ 0.124995814483 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037578365931 + 0.053361155313 * 1.772454 / (2 * (110.848256639425 : ℝ))) * (1 + 0.001215392821) +
        8 / (12424 * 111.462998344742) + 0.124995814483 := by gcongr
    _ ≤ (0.163052768462 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053361155313)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412133586) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284070774190) :
    parallelOracle 12424 0.011 xi bn cd ≤ 0.164069309416 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12424 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12424 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560490809473 : ℝ) ≤ plow 12424 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.462998344742 : ℝ) ≤ √(12424 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284070774190 : ℝ) / (2 * 0.560490809473 * 111.462998344742)) * 0.163052768462 +
        0.284070774190 ^ 2 / (2 * 0.560490809473 * 111.462998344742) := by gcongr
    _ ≤ (0.164069309416 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053361155313) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001412133586)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284070774190) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12424 12424 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560490809473 : ℝ) ≤ plow 12424 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.462998344742 : ℝ) ≤ √(12424 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12424 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12424 Θ 1.22 ≤ 0.011897226162 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.462998344742 := by gcongr <;> linarith
      _ ≤ (0.011897226162 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12424 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12424 12424 0.011 ≤ 0.008575824488 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12424 12424 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12424 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12424 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12424 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12424 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164069309416 + 0.011897226162 + (0.008575824488 : ℝ) *
        (1 + 2 * (0.284070774190 + 0.011897226162) / (0.560490809473 * 111.462998344742))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12424]

end BstLean.Part269.N12424

/-! The original eight local profiles supply actual 12424 moment certificates. -/
namespace BstLean.Part269.N12424
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12424 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12424 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12424 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053361155313 ∧
    0 ≤ bN 12424 BstLean.Part154.csC (groupTheta g) ∧ bN 12424 BstLean.Part154.csC (groupTheta g) ≤ 0.001412133586 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12424 12424 0.011
      (momentAllowance 12424 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12424 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12424 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12424 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12424 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12424 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231000336176 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12424 0.011
      (momentAllowance 12424 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12424 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12424
/-! The actual computed-centre upper energy formula at 12424. -/
namespace BstLean.Part269.N12424
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12424

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12424
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12424)
open BstLean.Part268 (cell12424)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086340655381
  | 2 => 0.087300109528
  | 3 => 0.088260310145
  | 4 => 0.089223262460
  | 5 => 0.090191370192
  | 6 => 0.091167491845
  | 7 => 0.092155001771
  | 8 => 0.093157855974
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12424 12424 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12424 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004091684411 + 0.003376189719 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S2.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S2.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12424

/-! Actual upper energy certificates on all 43 source endpoints at 12424. -/
namespace BstLean.Part269.N12424
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12424)
open BstLean.Part268 (cell12424)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12424 (gMinus 12424) (1 - (cell12424 i).lower) ≤ 1 ∧
    energyUpper 12424 (gMinus 12424) (BstLean.Part211.gPlus 12424)
      (finiteEnergy 12424 12424 0.011) (1 - (cell12424 i).lower) ≤
      (cell12424 i).energy := by
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
      have E := BstLean.Part269.S2.uniformEnergy10 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨10,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy11 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨11,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy12 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨12,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy13 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨13,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy14 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨14,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy15 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨15,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy16 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨16,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy17 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨17,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy18 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨18,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy19 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨19,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy20 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨20,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy21 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨21,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy22 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨22,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy23 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨23,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy24 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨24,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy25 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨25,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy26 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨26,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy27 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨27,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy28 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨28,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy29 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨29,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy30 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨30,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy31 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨31,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy32 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨32,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy33 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨33,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy34 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨34,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy35 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨35,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy36 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨36,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy37 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨37,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy38 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨38,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy39 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨39,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy40 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨40,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy41 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨41,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy42 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨42,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy43 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨43,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy44 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨44,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy45 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨45,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy46 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨46,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy47 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨47,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy48 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨48,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy49 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨49,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy50 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨50,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy51 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨51,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S2.uniformEnergy52 (n := 12424) (by norm_num)
        (q := 1 - (cell12424 ⟨52,by decide⟩).lower)
        (by norm_num [cell12424]) (by norm_num [cell12424])
      exact ⟨E.1,E.2.trans (by norm_num [cell12424])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12424

/-! Source-cell containment and simple scalar guards at 12424. -/
namespace BstLean.Part269.N12424
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12424)
open BstLean.Part268 (cell12424)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12424 ⟨10,by decide⟩).lower ∧ (cell12424 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12424 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12424 ⟨11,by decide⟩).lower ∧ (cell12424 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12424 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12424 ⟨12,by decide⟩).lower ∧ (cell12424 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12424 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12424 ⟨13,by decide⟩).lower ∧ (cell12424 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12424 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12424 ⟨14,by decide⟩).lower ∧ (cell12424 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12424 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12424 ⟨15,by decide⟩).lower ∧ (cell12424 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12424 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12424 ⟨16,by decide⟩).lower ∧ (cell12424 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12424 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12424 ⟨17,by decide⟩).lower ∧ (cell12424 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12424 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12424 ⟨18,by decide⟩).lower ∧ (cell12424 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12424 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12424 ⟨19,by decide⟩).lower ∧ (cell12424 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12424 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12424 ⟨20,by decide⟩).lower ∧ (cell12424 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12424 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12424 ⟨21,by decide⟩).lower ∧ (cell12424 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12424 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12424 ⟨22,by decide⟩).lower ∧ (cell12424 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12424 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12424 ⟨23,by decide⟩).lower ∧ (cell12424 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12424 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12424 ⟨24,by decide⟩).lower ∧ (cell12424 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12424 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12424 ⟨25,by decide⟩).lower ∧ (cell12424 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12424 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12424 ⟨26,by decide⟩).lower ∧ (cell12424 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12424 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12424 ⟨27,by decide⟩).lower ∧ (cell12424 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12424 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12424 ⟨28,by decide⟩).lower ∧ (cell12424 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12424 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12424 ⟨29,by decide⟩).lower ∧ (cell12424 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12424 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12424 ⟨30,by decide⟩).lower ∧ (cell12424 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12424 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12424 ⟨31,by decide⟩).lower ∧ (cell12424 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12424 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12424 ⟨32,by decide⟩).lower ∧ (cell12424 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12424 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12424 ⟨33,by decide⟩).lower ∧ (cell12424 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12424 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12424 ⟨34,by decide⟩).lower ∧ (cell12424 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12424 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12424 ⟨35,by decide⟩).lower ∧ (cell12424 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12424 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12424 ⟨36,by decide⟩).lower ∧ (cell12424 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12424 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12424 ⟨37,by decide⟩).lower ∧ (cell12424 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12424 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12424 ⟨38,by decide⟩).lower ∧ (cell12424 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12424 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12424 ⟨39,by decide⟩).lower ∧ (cell12424 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12424 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12424 ⟨40,by decide⟩).lower ∧ (cell12424 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12424 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12424 ⟨41,by decide⟩).lower ∧ (cell12424 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12424 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12424 ⟨42,by decide⟩).lower ∧ (cell12424 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12424 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12424 ⟨43,by decide⟩).lower ∧ (cell12424 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12424 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12424 ⟨44,by decide⟩).lower ∧ (cell12424 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12424 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12424 ⟨45,by decide⟩).lower ∧ (cell12424 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12424 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12424 ⟨46,by decide⟩).lower ∧ (cell12424 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12424 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12424 ⟨47,by decide⟩).lower ∧ (cell12424 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12424 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12424 ⟨48,by decide⟩).lower ∧ (cell12424 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12424 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12424 ⟨49,by decide⟩).lower ∧ (cell12424 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12424 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12424 ⟨50,by decide⟩).lower ∧ (cell12424 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12424 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12424 ⟨51,by decide⟩).lower ∧ (cell12424 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12424 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12424 ⟨52,by decide⟩).lower ∧ (cell12424 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12424 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12424 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12424 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12424,cell12424,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12424 i).lower ∧
    (cell12424 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12424 i).upper ≤ (0.532 : ℝ) ∧
    (cell12424 i).centre ≤ (0.1 : ℝ) ∧ (cell12424 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12424 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12424 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12424

/-! The local source numeric instances at 12424 have no network premises. -/
namespace BstLean.Part269.N12424
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12424)
open BstLean.Part268 (cell12424)

noncomputable def sourceNumerics12424 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12424 (cell12424 i)
      scalarRow12424.M scalarRow12424.H scalarRow12424.xi := by
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
    energy_allowance := scalarRow12424.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12424]
    centre_nonneg := (scalarRow12424.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D2.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12424])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12424