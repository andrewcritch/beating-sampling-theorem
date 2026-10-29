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
import BstLean.Part269Direction23
import BstLean.Part269Shared23
import BstLean.Part269Finite
import BstLean.Part269Rows23
import BstLean.Part269Source
/-! Actual 12925 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12925
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12925 ≤ (1.035493437527 : ℝ) := by
  have hr : (113.688170009020 : ℝ) ≤ √(12925 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.688170009020 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12925 12925 (11 / 1000) ≤
    (0.008407972132 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12925) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.688170009020 : ℝ) ≤ √(12925 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12925)
  have hdiv : K / √(12925 : ℝ) ≤ K / 113.688170009020 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.688170009020 ≤ (0.008407972132 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12925.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12925 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12925 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12925 := gPlus_lower 12925
end BstLean.Part269.N12925

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12925
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035493437526 : ℝ) ≤ wn 12925 := by
  have hn : √(12925 : ℝ) ≤ 113.688170009021 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12925 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.688170009021 ≤ 2 / √(12925 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247420642 : ℝ) ≤ rhoBar 12925 BstLean.Part154.csC ∧
    rhoBar 12925 BstLean.Part154.csC ≤ 0.000247421025 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035493437526 : ℝ) / (1.295212 * 12925) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035493437527 : ℝ) / (1.29521 * 12925) := by gcongr
      _ ≤ (0.000247421025 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12925 BstLean.Part154.csC) ≤ 0.000989745318 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12925 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12925 BstLean.Part154.csC) (piBar (rhoBar 12925 BstLean.Part154.csC)) ≤ 0.000188981692 ∧
    cc1 (rhoBar 12925 BstLean.Part154.csC) (piBar (rhoBar 12925 BstLean.Part154.csC)) ≤ 0.000120250338 ∧
    cc2 (rhoBar 12925 BstLean.Part154.csC) ≤ 0.000069806281 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12925 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12925 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12925 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12925 BstLean.Part154.csC * nuR (rhoBar 12925 BstLean.Part154.csC)) ≤ 0.000494857355 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247421025 : ℝ) * 0.000989745318 := by gcongr
      _ ≤ (0.000494857355 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12925 BstLean.Part154.csC) * nuR (rhoBar 12925 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000989745318 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12925 BstLean.Part154.csC) * rhoBar 12925 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247421025 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247421025 / 2 + 0.399 * 0.000989745318 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188981692 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494857355 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120250338 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247421025 / 1.414213562 := by gcongr
      _ ≤ (0.000069806281 : ℝ) := by norm_num

end BstLean.Part269.N12925

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12925
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12925 BstLean.Part154.csC) (piBar (rhoBar 12925 BstLean.Part154.csC)) ≤ 1.54232E-7 := by
  have hr0 : 0 ≤ rhoBar 12925 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12925 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12925 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12925 BstLean.Part154.csC) (piBar (rhoBar 12925 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12925 BstLean.Part154.csC) (piBar (rhoBar 12925 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12925 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188981692 : ℝ) ^ 2 + 0.000120250338 ^ 2 + 3 * 0.000069806281 ^ 2 +
        2 * 0.797885 * 0.000188981692 * 0.000120250338 + 2 * 0.000188981692 * 0.000069806281 +
        4 * 0.797885 * 0.000120250338 * 0.000069806281 := by gcongr
    _ ≤ (1.54232E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12925 BstLean.Part154.csC Θ ≤ 0.002581938558 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12925 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12925 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12925 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12925 BstLean.Part154.csC) (piBar (rhoBar 12925 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12925 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035493437527 * 1.54232E-7 / (0.000247420642 : ℝ) := by gcongr
    _ ≤ 0.002581938558 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12925 BstLean.Part154.csC Θ ≤ 0.002863928480 + 0.000652415331 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12925 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12925 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12925 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035493437527 : ℝ) * ((2 * Θ * 0.000247421025 +
        (6863 / 10000) * 0.000247421025 * 12925 * 0.000989745318) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002863928480 + 0.000652415331 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12925 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12925 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12925 0.011 Θ ∧ gammaRatio 12925 0.011 Θ ≤ 0.000085056951 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12925 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035493437527 : ℝ) * 0.525 / ((1 - 0.011) * 12925) := by gcongr
      _ ≤ (0.000085056951 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12925 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12925 0.011 Θ) :=
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
    badAllowance 12925 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12925 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12925 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12925 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12925 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12925 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12925 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12925 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12925 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12925 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12925 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035493437527 : ℝ) * 12925 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12925 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003284487036 + 0.003234353889 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12925

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12925
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12925 BstLean.Part154.csC) (piBar (rhoBar 12925 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12925 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12925 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12925 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12925 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12925 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12925 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12925 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12925 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12925 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12925 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12925 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12925 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12925 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12925 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052020548636 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12925) ≤ 0.010504501753 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12925 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035493437527)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010504501753 + 2 * 0.737676 / 12925) := by gcongr
    _ ≤ (0.052020548636 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12925 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12925

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12925
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513566328 : ℝ) ≤ plow 12925 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12925) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052489122828)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355517743) : eMP 12925 0.011 xi bn ≤ 0.001167267704 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12925 : ℝ) * (1 - 0.011))) ≤ 0.000577183812 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001355517743 / (12925 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577183812 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577183812 : ℝ) + 3.141593 * 0.052489122828 / (12925 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001167267704 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052489122828)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355517743) : PiBarMP 12925 12 0.011 xi bn ≤ 0.159827014452 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12925 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036817356546 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.061156017440 : ℝ) ≤ √((12925 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.688170009020 : ℝ) ≤ √(12925 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12925) ≤ 0.122549322957 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036817356546 + 0.052489122828 * 1.772454 / (2 * (113.061156017440 : ℝ))) * (1 + 0.001167267704) +
        8 / (12925 * 113.688170009020) + 0.122549322957 := by gcongr
    _ ≤ (0.159827014452 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052489122828)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355517743) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281125596219) :
    parallelOracle 12925 0.011 xi bn cd ≤ 0.160799674120 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12925 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12925 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513566328 : ℝ) ≤ plow 12925 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.688170009020 : ℝ) ≤ √(12925 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281125596219 : ℝ) / (2 * 0.560513566328 * 113.688170009020)) * 0.159827014452 +
        0.281125596219 ^ 2 / (2 * 0.560513566328 * 113.688170009020) := by gcongr
    _ ≤ (0.160799674120 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052489122828) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355517743)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281125596219) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12925 12925 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513566328 : ℝ) ≤ plow 12925 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.688170009020 : ℝ) ≤ √(12925 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12925 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12925 Θ 1.22 ≤ 0.011664366661 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.688170009020 := by gcongr <;> linarith
      _ ≤ (0.011664366661 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12925 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12925 12925 0.011 ≤ 0.008407972132 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12925 12925 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12925 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12925 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12925 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12925 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160799674120 + 0.011664366661 + (0.008407972132 : ℝ) *
        (1 + 2 * (0.281125596219 + 0.011664366661) / (0.560513566328 * 113.688170009020))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12925]

end BstLean.Part269.N12925

/-! The original eight local profiles supply actual 12925 moment certificates. -/
namespace BstLean.Part269.N12925
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12925 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12925 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12925 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052489122828 ∧
    0 ≤ bN 12925 BstLean.Part154.csC (groupTheta g) ∧ bN 12925 BstLean.Part154.csC (groupTheta g) ≤ 0.001355517743 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12925 12925 0.011
      (momentAllowance 12925 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12925 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12925 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12925 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12925 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12925 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229105047583 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12925 0.011
      (momentAllowance 12925 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12925 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12925
/-! The actual computed-centre upper energy formula at 12925. -/
namespace BstLean.Part269.N12925
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12925

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12925
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12925)
open BstLean.Part268 (cell12925)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084859585502
  | 2 => 0.085791304047
  | 3 => 0.086719644511
  | 4 => 0.087645669285
  | 5 => 0.088570674102
  | 6 => 0.089496224040
  | 7 => 0.090424193171
  | 8 => 0.091356807932
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12925 12925 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12925 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12925

/-! Actual upper energy certificates on all 43 source endpoints at 12925. -/
namespace BstLean.Part269.N12925
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12925)
open BstLean.Part268 (cell12925)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12925 (gMinus 12925) (1 - (cell12925 i).lower) ≤ 1 ∧
    energyUpper 12925 (gMinus 12925) (BstLean.Part211.gPlus 12925)
      (finiteEnergy 12925 12925 0.011) (1 - (cell12925 i).lower) ≤
      (cell12925 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨10,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨11,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨12,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨13,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨14,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨15,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨16,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨17,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨18,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨19,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨20,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨21,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨22,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨23,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨24,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨25,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨26,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨27,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨28,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨29,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨30,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨31,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨32,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨33,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨34,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨35,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨36,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨37,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨38,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨39,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨40,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨41,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨42,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨43,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨44,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨45,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨46,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨47,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨48,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨49,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨50,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨51,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12925) (by norm_num)
        (q := 1 - (cell12925 ⟨52,by decide⟩).lower)
        (by norm_num [cell12925]) (by norm_num [cell12925])
      exact ⟨E.1,E.2.trans (by norm_num [cell12925])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12925

/-! Source-cell containment and simple scalar guards at 12925. -/
namespace BstLean.Part269.N12925
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12925)
open BstLean.Part268 (cell12925)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12925 ⟨10,by decide⟩).lower ∧ (cell12925 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12925 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12925 ⟨11,by decide⟩).lower ∧ (cell12925 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12925 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12925 ⟨12,by decide⟩).lower ∧ (cell12925 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12925 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12925 ⟨13,by decide⟩).lower ∧ (cell12925 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12925 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12925 ⟨14,by decide⟩).lower ∧ (cell12925 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12925 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12925 ⟨15,by decide⟩).lower ∧ (cell12925 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12925 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12925 ⟨16,by decide⟩).lower ∧ (cell12925 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12925 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12925 ⟨17,by decide⟩).lower ∧ (cell12925 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12925 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12925 ⟨18,by decide⟩).lower ∧ (cell12925 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12925 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12925 ⟨19,by decide⟩).lower ∧ (cell12925 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12925 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12925 ⟨20,by decide⟩).lower ∧ (cell12925 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12925 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12925 ⟨21,by decide⟩).lower ∧ (cell12925 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12925 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12925 ⟨22,by decide⟩).lower ∧ (cell12925 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12925 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12925 ⟨23,by decide⟩).lower ∧ (cell12925 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12925 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12925 ⟨24,by decide⟩).lower ∧ (cell12925 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12925 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12925 ⟨25,by decide⟩).lower ∧ (cell12925 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12925 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12925 ⟨26,by decide⟩).lower ∧ (cell12925 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12925 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12925 ⟨27,by decide⟩).lower ∧ (cell12925 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12925 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12925 ⟨28,by decide⟩).lower ∧ (cell12925 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12925 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12925 ⟨29,by decide⟩).lower ∧ (cell12925 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12925 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12925 ⟨30,by decide⟩).lower ∧ (cell12925 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12925 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12925 ⟨31,by decide⟩).lower ∧ (cell12925 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12925 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12925 ⟨32,by decide⟩).lower ∧ (cell12925 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12925 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12925 ⟨33,by decide⟩).lower ∧ (cell12925 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12925 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12925 ⟨34,by decide⟩).lower ∧ (cell12925 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12925 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12925 ⟨35,by decide⟩).lower ∧ (cell12925 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12925 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12925 ⟨36,by decide⟩).lower ∧ (cell12925 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12925 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12925 ⟨37,by decide⟩).lower ∧ (cell12925 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12925 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12925 ⟨38,by decide⟩).lower ∧ (cell12925 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12925 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12925 ⟨39,by decide⟩).lower ∧ (cell12925 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12925 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12925 ⟨40,by decide⟩).lower ∧ (cell12925 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12925 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12925 ⟨41,by decide⟩).lower ∧ (cell12925 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12925 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12925 ⟨42,by decide⟩).lower ∧ (cell12925 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12925 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12925 ⟨43,by decide⟩).lower ∧ (cell12925 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12925 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12925 ⟨44,by decide⟩).lower ∧ (cell12925 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12925 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12925 ⟨45,by decide⟩).lower ∧ (cell12925 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12925 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12925 ⟨46,by decide⟩).lower ∧ (cell12925 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12925 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12925 ⟨47,by decide⟩).lower ∧ (cell12925 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12925 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12925 ⟨48,by decide⟩).lower ∧ (cell12925 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12925 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12925 ⟨49,by decide⟩).lower ∧ (cell12925 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12925 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12925 ⟨50,by decide⟩).lower ∧ (cell12925 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12925 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12925 ⟨51,by decide⟩).lower ∧ (cell12925 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12925 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12925 ⟨52,by decide⟩).lower ∧ (cell12925 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12925 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12925 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12925 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12925,cell12925,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12925 i).lower ∧
    (cell12925 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12925 i).upper ≤ (0.532 : ℝ) ∧
    (cell12925 i).centre ≤ (0.1 : ℝ) ∧ (cell12925 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12925 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12925 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12925

/-! The local source numeric instances at 12925 have no network premises. -/
namespace BstLean.Part269.N12925
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12925)
open BstLean.Part268 (cell12925)

noncomputable def sourceNumerics12925 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12925 (cell12925 i)
      scalarRow12925.M scalarRow12925.H scalarRow12925.xi := by
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
    energy_allowance := scalarRow12925.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12925]
    centre_nonneg := (scalarRow12925.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12925])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12925
/-! Actual 12926 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12926
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12926 ≤ (1.035492052583 : ℝ) := by
  have hr : (113.692567918927 : ℝ) ≤ √(12926 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.692567918927 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12926 12926 (11 / 1000) ≤
    (0.008407646888 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12926) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.692567918927 : ℝ) ≤ √(12926 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12926)
  have hdiv : K / √(12926 : ℝ) ≤ K / 113.692567918927 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.692567918927 ≤ (0.008407646888 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12926.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12926 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12926 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12926 := gPlus_lower 12926
end BstLean.Part269.N12926

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12926
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035492052582 : ℝ) ≤ wn 12926 := by
  have hn : √(12926 : ℝ) ≤ 113.692567918928 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12926 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.692567918928 ≤ 2 / √(12926 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247401170 : ℝ) ≤ rhoBar 12926 BstLean.Part154.csC ∧
    rhoBar 12926 BstLean.Part154.csC ≤ 0.000247401553 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035492052582 : ℝ) / (1.295212 * 12926) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035492052583 : ℝ) / (1.29521 * 12926) := by gcongr
      _ ≤ (0.000247401553 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12926 BstLean.Part154.csC) ≤ 0.000989667420 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12926 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12926 BstLean.Part154.csC) (piBar (rhoBar 12926 BstLean.Part154.csC)) ≤ 0.000188966819 ∧
    cc1 (rhoBar 12926 BstLean.Part154.csC) (piBar (rhoBar 12926 BstLean.Part154.csC)) ≤ 0.000120240874 ∧
    cc2 (rhoBar 12926 BstLean.Part154.csC) ≤ 0.000069800788 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12926 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12926 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12926 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12926 BstLean.Part154.csC * nuR (rhoBar 12926 BstLean.Part154.csC)) ≤ 0.000494818408 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247401553 : ℝ) * 0.000989667420 := by gcongr
      _ ≤ (0.000494818408 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12926 BstLean.Part154.csC) * nuR (rhoBar 12926 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000989667420 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12926 BstLean.Part154.csC) * rhoBar 12926 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247401553 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247401553 / 2 + 0.399 * 0.000989667420 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188966819 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494818408 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120240874 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247401553 / 1.414213562 := by gcongr
      _ ≤ (0.000069800788 : ℝ) := by norm_num

end BstLean.Part269.N12926

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12926
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12926 BstLean.Part154.csC) (piBar (rhoBar 12926 BstLean.Part154.csC)) ≤ 1.54208E-7 := by
  have hr0 : 0 ≤ rhoBar 12926 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12926 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12926 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12926 BstLean.Part154.csC) (piBar (rhoBar 12926 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12926 BstLean.Part154.csC) (piBar (rhoBar 12926 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12926 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188966819 : ℝ) ^ 2 + 0.000120240874 ^ 2 + 3 * 0.000069800788 ^ 2 +
        2 * 0.797885 * 0.000188966819 * 0.000120240874 + 2 * 0.000188966819 * 0.000069800788 +
        4 * 0.797885 * 0.000120240874 * 0.000069800788 := by gcongr
    _ ≤ (1.54208E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12926 BstLean.Part154.csC Θ ≤ 0.002581736513 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12926 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12926 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12926 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12926 BstLean.Part154.csC) (piBar (rhoBar 12926 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12926 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035492052583 * 1.54208E-7 / (0.000247401170 : ℝ) := by gcongr
    _ ≤ 0.002581736513 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12926 BstLean.Part154.csC Θ ≤ 0.002863695417 + 0.000652363113 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12926 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12926 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12926 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035492052583 : ℝ) * ((2 * Θ * 0.000247401553 +
        (6863 / 10000) * 0.000247401553 * 12926 * 0.000989667420) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002863695417 + 0.000652363113 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12926 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12926 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12926 0.011 Θ ∧ gammaRatio 12926 0.011 Θ ≤ 0.000085050257 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12926 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035492052583 : ℝ) * 0.525 / ((1 - 0.011) * 12926) := by gcongr
      _ ≤ (0.000085050257 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12926 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12926 0.011 Θ) :=
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
    badAllowance 12926 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12926 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12926 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12926 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12926 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12926 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12926 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12926 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12926 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12926 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12926 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035492052583 : ℝ) * 12926 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12926 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003284253973 + 0.003234099626 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12926

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12926
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12926 BstLean.Part154.csC) (piBar (rhoBar 12926 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12926 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12926 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12926 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12926 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12926 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12926 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12926 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12926 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12926 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12926 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12926 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12926 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12926 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12926 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052018514718 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12926) ≤ 0.010504095412 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12926 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035492052583)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010504095412 + 2 * 0.737676 / 12926) := by gcongr
    _ ≤ (0.052018514718 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12926 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12926

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12926
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513609987 : ℝ) ≤ plow 12926 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12926) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052488756277)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355411670) : eMP 12926 0.011 xi bn ≤ 0.001167176798 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12926 : ℝ) * (1 - 0.011))) ≤ 0.000577138903 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001355411670 / (12926 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577138903 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577138903 : ℝ) + 3.141593 * 0.052488756277 / (12926 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001167176798 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052488756277)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355411670) : PiBarMP 12926 12 0.011 xi bn ≤ 0.159820808875 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12926 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036815915988 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.065529671956 : ℝ) ≤ √((12926 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.692567918927 : ℝ) ≤ √(12926 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12926) ≤ 0.122544582446 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036815915988 + 0.052488756277 * 1.772454 / (2 * (113.065529671956 : ℝ))) * (1 + 0.001167176798) +
        8 / (12926 * 113.692567918927) + 0.122544582446 := by gcongr
    _ ≤ (0.159820808875 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052488756277)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355411670) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281122762337) :
    parallelOracle 12926 0.011 xi bn cd ≤ 0.160793401099 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12926 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12926 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513609987 : ℝ) ≤ plow 12926 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.692567918927 : ℝ) ≤ √(12926 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281122762337 : ℝ) / (2 * 0.560513609987 * 113.692567918927)) * 0.159820808875 +
        0.281122762337 ^ 2 / (2 * 0.560513609987 * 113.692567918927) := by gcongr
    _ ≤ (0.160793401099 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052488756277) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355411670)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281122762337) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12926 12926 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513609987 : ℝ) ≤ plow 12926 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.692567918927 : ℝ) ≤ √(12926 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12926 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12926 Θ 1.22 ≤ 0.011663915455 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.692567918927 := by gcongr <;> linarith
      _ ≤ (0.011663915455 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12926 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12926 12926 0.011 ≤ 0.008407646888 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12926 12926 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12926 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12926 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12926 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12926 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160793401099 + 0.011663915455 + (0.008407646888 : ℝ) *
        (1 + 2 * (0.281122762337 + 0.011663915455) / (0.560513609987 * 113.692567918927))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12926]

end BstLean.Part269.N12926

/-! The original eight local profiles supply actual 12926 moment certificates. -/
namespace BstLean.Part269.N12926
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12926 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12926 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12926 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052488756277 ∧
    0 ≤ bN 12926 BstLean.Part154.csC (groupTheta g) ∧ bN 12926 BstLean.Part154.csC (groupTheta g) ≤ 0.001355411670 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12926 12926 0.011
      (momentAllowance 12926 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12926 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12926 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12926 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12926 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12926 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229104247619 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12926 0.011
      (momentAllowance 12926 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12926 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12926
/-! The actual computed-centre upper energy formula at 12926. -/
namespace BstLean.Part269.N12926
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12926

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12926
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12926)
open BstLean.Part268 (cell12926)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084856888236
  | 2 => 0.085788561907
  | 3 => 0.086716851727
  | 4 => 0.087642818710
  | 5 => 0.088567756959
  | 6 => 0.089493229637
  | 7 => 0.090421108581
  | 8 => 0.091353617638
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12926 12926 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12926 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12926

/-! Actual upper energy certificates on all 43 source endpoints at 12926. -/
namespace BstLean.Part269.N12926
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12926)
open BstLean.Part268 (cell12926)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12926 (gMinus 12926) (1 - (cell12926 i).lower) ≤ 1 ∧
    energyUpper 12926 (gMinus 12926) (BstLean.Part211.gPlus 12926)
      (finiteEnergy 12926 12926 0.011) (1 - (cell12926 i).lower) ≤
      (cell12926 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨10,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨11,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨12,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨13,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨14,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨15,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨16,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨17,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨18,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨19,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨20,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨21,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨22,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨23,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨24,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨25,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨26,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨27,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨28,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨29,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨30,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨31,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨32,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨33,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨34,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨35,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨36,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨37,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨38,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨39,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨40,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨41,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨42,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨43,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨44,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨45,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨46,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨47,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨48,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨49,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨50,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨51,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12926) (by norm_num)
        (q := 1 - (cell12926 ⟨52,by decide⟩).lower)
        (by norm_num [cell12926]) (by norm_num [cell12926])
      exact ⟨E.1,E.2.trans (by norm_num [cell12926])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12926

/-! Source-cell containment and simple scalar guards at 12926. -/
namespace BstLean.Part269.N12926
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12926)
open BstLean.Part268 (cell12926)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12926 ⟨10,by decide⟩).lower ∧ (cell12926 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12926 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12926 ⟨11,by decide⟩).lower ∧ (cell12926 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12926 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12926 ⟨12,by decide⟩).lower ∧ (cell12926 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12926 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12926 ⟨13,by decide⟩).lower ∧ (cell12926 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12926 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12926 ⟨14,by decide⟩).lower ∧ (cell12926 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12926 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12926 ⟨15,by decide⟩).lower ∧ (cell12926 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12926 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12926 ⟨16,by decide⟩).lower ∧ (cell12926 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12926 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12926 ⟨17,by decide⟩).lower ∧ (cell12926 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12926 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12926 ⟨18,by decide⟩).lower ∧ (cell12926 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12926 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12926 ⟨19,by decide⟩).lower ∧ (cell12926 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12926 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12926 ⟨20,by decide⟩).lower ∧ (cell12926 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12926 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12926 ⟨21,by decide⟩).lower ∧ (cell12926 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12926 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12926 ⟨22,by decide⟩).lower ∧ (cell12926 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12926 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12926 ⟨23,by decide⟩).lower ∧ (cell12926 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12926 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12926 ⟨24,by decide⟩).lower ∧ (cell12926 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12926 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12926 ⟨25,by decide⟩).lower ∧ (cell12926 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12926 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12926 ⟨26,by decide⟩).lower ∧ (cell12926 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12926 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12926 ⟨27,by decide⟩).lower ∧ (cell12926 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12926 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12926 ⟨28,by decide⟩).lower ∧ (cell12926 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12926 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12926 ⟨29,by decide⟩).lower ∧ (cell12926 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12926 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12926 ⟨30,by decide⟩).lower ∧ (cell12926 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12926 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12926 ⟨31,by decide⟩).lower ∧ (cell12926 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12926 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12926 ⟨32,by decide⟩).lower ∧ (cell12926 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12926 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12926 ⟨33,by decide⟩).lower ∧ (cell12926 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12926 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12926 ⟨34,by decide⟩).lower ∧ (cell12926 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12926 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12926 ⟨35,by decide⟩).lower ∧ (cell12926 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12926 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12926 ⟨36,by decide⟩).lower ∧ (cell12926 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12926 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12926 ⟨37,by decide⟩).lower ∧ (cell12926 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12926 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12926 ⟨38,by decide⟩).lower ∧ (cell12926 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12926 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12926 ⟨39,by decide⟩).lower ∧ (cell12926 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12926 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12926 ⟨40,by decide⟩).lower ∧ (cell12926 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12926 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12926 ⟨41,by decide⟩).lower ∧ (cell12926 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12926 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12926 ⟨42,by decide⟩).lower ∧ (cell12926 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12926 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12926 ⟨43,by decide⟩).lower ∧ (cell12926 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12926 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12926 ⟨44,by decide⟩).lower ∧ (cell12926 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12926 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12926 ⟨45,by decide⟩).lower ∧ (cell12926 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12926 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12926 ⟨46,by decide⟩).lower ∧ (cell12926 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12926 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12926 ⟨47,by decide⟩).lower ∧ (cell12926 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12926 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12926 ⟨48,by decide⟩).lower ∧ (cell12926 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12926 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12926 ⟨49,by decide⟩).lower ∧ (cell12926 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12926 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12926 ⟨50,by decide⟩).lower ∧ (cell12926 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12926 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12926 ⟨51,by decide⟩).lower ∧ (cell12926 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12926 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12926 ⟨52,by decide⟩).lower ∧ (cell12926 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12926 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12926 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12926 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12926,cell12926,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12926 i).lower ∧
    (cell12926 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12926 i).upper ≤ (0.532 : ℝ) ∧
    (cell12926 i).centre ≤ (0.1 : ℝ) ∧ (cell12926 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12926 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12926 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12926

/-! The local source numeric instances at 12926 have no network premises. -/
namespace BstLean.Part269.N12926
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12926)
open BstLean.Part268 (cell12926)

noncomputable def sourceNumerics12926 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12926 (cell12926 i)
      scalarRow12926.M scalarRow12926.H scalarRow12926.xi := by
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
    energy_allowance := scalarRow12926.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12926]
    centre_nonneg := (scalarRow12926.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12926])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12926
/-! Actual 12927 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12927
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12927 ≤ (1.035490667799 : ℝ) := by
  have hr : (113.696965658719 : ℝ) ≤ √(12927 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.696965658719 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12927 12927 (11 / 1000) ≤
    (0.008407321682 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12927) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.696965658719 : ℝ) ≤ √(12927 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12927)
  have hdiv : K / √(12927 : ℝ) ≤ K / 113.696965658719 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.696965658719 ≤ (0.008407321682 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12927.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12927 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12927 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12927 := gPlus_lower 12927
end BstLean.Part269.N12927

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12927
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035490667798 : ℝ) ≤ wn 12927 := by
  have hn : √(12927 : ℝ) ≤ 113.696965658720 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12927 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.696965658720 ≤ 2 / √(12927 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247381701 : ℝ) ≤ rhoBar 12927 BstLean.Part154.csC ∧
    rhoBar 12927 BstLean.Part154.csC ≤ 0.000247382084 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035490667798 : ℝ) / (1.295212 * 12927) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035490667799 : ℝ) / (1.29521 * 12927) := by gcongr
      _ ≤ (0.000247382084 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12927 BstLean.Part154.csC) ≤ 0.000989589534 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12927 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12927 BstLean.Part154.csC) (piBar (rhoBar 12927 BstLean.Part154.csC)) ≤ 0.000188951948 ∧
    cc1 (rhoBar 12927 BstLean.Part154.csC) (piBar (rhoBar 12927 BstLean.Part154.csC)) ≤ 0.000120231411 ∧
    cc2 (rhoBar 12927 BstLean.Part154.csC) ≤ 0.000069795295 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12927 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12927 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12927 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12927 BstLean.Part154.csC * nuR (rhoBar 12927 BstLean.Part154.csC)) ≤ 0.000494779468 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247382084 : ℝ) * 0.000989589534 := by gcongr
      _ ≤ (0.000494779468 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12927 BstLean.Part154.csC) * nuR (rhoBar 12927 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000989589534 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12927 BstLean.Part154.csC) * rhoBar 12927 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247382084 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247382084 / 2 + 0.399 * 0.000989589534 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188951948 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494779468 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120231411 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247382084 / 1.414213562 := by gcongr
      _ ≤ (0.000069795295 : ℝ) := by norm_num

end BstLean.Part269.N12927

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12927
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12927 BstLean.Part154.csC) (piBar (rhoBar 12927 BstLean.Part154.csC)) ≤ 1.54184E-7 := by
  have hr0 : 0 ≤ rhoBar 12927 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12927 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12927 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12927 BstLean.Part154.csC) (piBar (rhoBar 12927 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12927 BstLean.Part154.csC) (piBar (rhoBar 12927 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12927 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188951948 : ℝ) ^ 2 + 0.000120231411 ^ 2 + 3 * 0.000069795295 ^ 2 +
        2 * 0.797885 * 0.000188951948 * 0.000120231411 + 2 * 0.000188951948 * 0.000069795295 +
        4 * 0.797885 * 0.000120231411 * 0.000069795295 := by gcongr
    _ ≤ (1.54184E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12927 BstLean.Part154.csC Θ ≤ 0.002581534406 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12927 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12927 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12927 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12927 BstLean.Part154.csC) (piBar (rhoBar 12927 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12927 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035490667799 * 1.54184E-7 / (0.000247381701 : ℝ) := by gcongr
    _ ≤ 0.002581534406 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12927 BstLean.Part154.csC Θ ≤ 0.002863462390 + 0.000652310904 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12927 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12927 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12927 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035490667799 : ℝ) * ((2 * Θ * 0.000247382084 +
        (6863 / 10000) * 0.000247382084 * 12927 * 0.000989589534) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002863462390 + 0.000652310904 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12927 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12927 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12927 0.011 Θ ∧ gammaRatio 12927 0.011 Θ ≤ 0.000085043564 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12927 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035490667799 : ℝ) * 0.525 / ((1 - 0.011) * 12927) := by gcongr
      _ ≤ (0.000085043564 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12927 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12927 0.011 Θ) :=
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
    badAllowance 12927 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12927 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12927 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12927 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12927 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12927 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12927 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12927 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12927 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12927 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12927 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035490667799 : ℝ) * 12927 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12927 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003284020946 + 0.003233845310 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12927

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12927
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12927 BstLean.Part154.csC) (piBar (rhoBar 12927 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12927 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12927 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12927 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12927 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12927 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12927 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12927 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12927 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12927 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12927 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12927 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12927 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12927 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12927 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052016481046 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12927) ≤ 0.010503689120 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12927 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035490667799)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010503689120 + 2 * 0.737676 / 12927) := by gcongr
    _ ≤ (0.052016481046 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12927 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12927

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12927
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513653639 : ℝ) ≤ plow 12927 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12927) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052488389734)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355305564) : eMP 12927 0.011 xi bn ≤ 0.001167085882 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12927 : ℝ) * (1 - 0.011))) ≤ 0.000577093989 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001355305564 / (12927 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577093989 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577093989 : ℝ) + 3.141593 * 0.052488389734 / (12927 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001167085882 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052488389734)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355305564) : PiBarMP 12927 12 0.011 xi bn ≤ 0.159814603345 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12927 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036814474925 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.069903157294 : ℝ) ≤ √((12927 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.696965658719 : ℝ) ≤ √(12927 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12927) ≤ 0.122539842485 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036814474925 + 0.052488389734 * 1.772454 / (2 * (113.069903157294 : ℝ))) * (1 + 0.001167085882) +
        8 / (12927 * 113.696965658719) + 0.122539842485 := by gcongr
    _ ≤ (0.159814603345 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052488389734)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355305564) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281119928716) :
    parallelOracle 12927 0.011 xi bn cd ≤ 0.160787128135 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12927 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12927 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513653639 : ℝ) ≤ plow 12927 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.696965658719 : ℝ) ≤ √(12927 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281119928716 : ℝ) / (2 * 0.560513653639 * 113.696965658719)) * 0.159814603345 +
        0.281119928716 ^ 2 / (2 * 0.560513653639 * 113.696965658719) := by gcongr
    _ ≤ (0.160787128135 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052488389734) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355305564)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281119928716) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12927 12927 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513653639 : ℝ) ≤ plow 12927 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.696965658719 : ℝ) ≤ √(12927 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12927 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12927 Θ 1.22 ≤ 0.011663464301 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.696965658719 := by gcongr <;> linarith
      _ ≤ (0.011663464301 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12927 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12927 12927 0.011 ≤ 0.008407321682 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12927 12927 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12927 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12927 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12927 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12927 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160787128135 + 0.011663464301 + (0.008407321682 : ℝ) *
        (1 + 2 * (0.281119928716 + 0.011663464301) / (0.560513653639 * 113.696965658719))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12927]

end BstLean.Part269.N12927

/-! The original eight local profiles supply actual 12927 moment certificates. -/
namespace BstLean.Part269.N12927
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12927 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12927 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12927 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052488389734 ∧
    0 ≤ bN 12927 BstLean.Part154.csC (groupTheta g) ∧ bN 12927 BstLean.Part154.csC (groupTheta g) ≤ 0.001355305564 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12927 12927 0.011
      (momentAllowance 12927 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12927 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12927 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12927 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12927 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12927 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229103447670 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12927 0.011
      (momentAllowance 12927 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12927 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12927
/-! The actual computed-centre upper energy formula at 12927. -/
namespace BstLean.Part269.N12927
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12927

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12927
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12927)
open BstLean.Part268 (cell12927)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084854191839
  | 2 => 0.085785820668
  | 3 => 0.086714059886
  | 4 => 0.087639969129
  | 5 => 0.088564840871
  | 6 => 0.089490236364
  | 7 => 0.090418025214
  | 8 => 0.091350428677
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12927 12927 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12927 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12927

/-! Actual upper energy certificates on all 43 source endpoints at 12927. -/
namespace BstLean.Part269.N12927
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12927)
open BstLean.Part268 (cell12927)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12927 (gMinus 12927) (1 - (cell12927 i).lower) ≤ 1 ∧
    energyUpper 12927 (gMinus 12927) (BstLean.Part211.gPlus 12927)
      (finiteEnergy 12927 12927 0.011) (1 - (cell12927 i).lower) ≤
      (cell12927 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨10,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨11,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨12,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨13,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨14,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨15,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨16,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨17,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨18,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨19,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨20,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨21,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨22,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨23,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨24,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨25,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨26,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨27,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨28,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨29,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨30,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨31,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨32,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨33,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨34,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨35,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨36,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨37,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨38,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨39,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨40,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨41,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨42,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨43,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨44,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨45,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨46,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨47,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨48,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨49,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨50,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨51,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12927) (by norm_num)
        (q := 1 - (cell12927 ⟨52,by decide⟩).lower)
        (by norm_num [cell12927]) (by norm_num [cell12927])
      exact ⟨E.1,E.2.trans (by norm_num [cell12927])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12927

/-! Source-cell containment and simple scalar guards at 12927. -/
namespace BstLean.Part269.N12927
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12927)
open BstLean.Part268 (cell12927)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12927 ⟨10,by decide⟩).lower ∧ (cell12927 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12927 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12927 ⟨11,by decide⟩).lower ∧ (cell12927 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12927 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12927 ⟨12,by decide⟩).lower ∧ (cell12927 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12927 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12927 ⟨13,by decide⟩).lower ∧ (cell12927 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12927 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12927 ⟨14,by decide⟩).lower ∧ (cell12927 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12927 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12927 ⟨15,by decide⟩).lower ∧ (cell12927 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12927 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12927 ⟨16,by decide⟩).lower ∧ (cell12927 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12927 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12927 ⟨17,by decide⟩).lower ∧ (cell12927 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12927 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12927 ⟨18,by decide⟩).lower ∧ (cell12927 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12927 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12927 ⟨19,by decide⟩).lower ∧ (cell12927 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12927 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12927 ⟨20,by decide⟩).lower ∧ (cell12927 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12927 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12927 ⟨21,by decide⟩).lower ∧ (cell12927 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12927 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12927 ⟨22,by decide⟩).lower ∧ (cell12927 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12927 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12927 ⟨23,by decide⟩).lower ∧ (cell12927 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12927 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12927 ⟨24,by decide⟩).lower ∧ (cell12927 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12927 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12927 ⟨25,by decide⟩).lower ∧ (cell12927 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12927 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12927 ⟨26,by decide⟩).lower ∧ (cell12927 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12927 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12927 ⟨27,by decide⟩).lower ∧ (cell12927 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12927 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12927 ⟨28,by decide⟩).lower ∧ (cell12927 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12927 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12927 ⟨29,by decide⟩).lower ∧ (cell12927 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12927 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12927 ⟨30,by decide⟩).lower ∧ (cell12927 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12927 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12927 ⟨31,by decide⟩).lower ∧ (cell12927 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12927 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12927 ⟨32,by decide⟩).lower ∧ (cell12927 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12927 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12927 ⟨33,by decide⟩).lower ∧ (cell12927 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12927 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12927 ⟨34,by decide⟩).lower ∧ (cell12927 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12927 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12927 ⟨35,by decide⟩).lower ∧ (cell12927 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12927 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12927 ⟨36,by decide⟩).lower ∧ (cell12927 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12927 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12927 ⟨37,by decide⟩).lower ∧ (cell12927 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12927 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12927 ⟨38,by decide⟩).lower ∧ (cell12927 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12927 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12927 ⟨39,by decide⟩).lower ∧ (cell12927 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12927 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12927 ⟨40,by decide⟩).lower ∧ (cell12927 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12927 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12927 ⟨41,by decide⟩).lower ∧ (cell12927 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12927 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12927 ⟨42,by decide⟩).lower ∧ (cell12927 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12927 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12927 ⟨43,by decide⟩).lower ∧ (cell12927 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12927 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12927 ⟨44,by decide⟩).lower ∧ (cell12927 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12927 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12927 ⟨45,by decide⟩).lower ∧ (cell12927 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12927 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12927 ⟨46,by decide⟩).lower ∧ (cell12927 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12927 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12927 ⟨47,by decide⟩).lower ∧ (cell12927 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12927 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12927 ⟨48,by decide⟩).lower ∧ (cell12927 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12927 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12927 ⟨49,by decide⟩).lower ∧ (cell12927 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12927 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12927 ⟨50,by decide⟩).lower ∧ (cell12927 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12927 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12927 ⟨51,by decide⟩).lower ∧ (cell12927 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12927 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12927 ⟨52,by decide⟩).lower ∧ (cell12927 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12927 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12927 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12927 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12927,cell12927,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12927 i).lower ∧
    (cell12927 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12927 i).upper ≤ (0.532 : ℝ) ∧
    (cell12927 i).centre ≤ (0.1 : ℝ) ∧ (cell12927 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12927 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12927 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12927

/-! The local source numeric instances at 12927 have no network premises. -/
namespace BstLean.Part269.N12927
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12927)
open BstLean.Part268 (cell12927)

noncomputable def sourceNumerics12927 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12927 (cell12927 i)
      scalarRow12927.M scalarRow12927.H scalarRow12927.xi := by
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
    energy_allowance := scalarRow12927.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12927]
    centre_nonneg := (scalarRow12927.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12927])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12927
/-! Actual 12928 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12928
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12928 ≤ (1.035489283178 : ℝ) := by
  have hr : (113.701363228415 : ℝ) ≤ √(12928 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.701363228415 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12928 12928 (11 / 1000) ≤
    (0.008406996514 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12928) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.701363228415 : ℝ) ≤ √(12928 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12928)
  have hdiv : K / √(12928 : ℝ) ≤ K / 113.701363228415 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.701363228415 ≤ (0.008406996514 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12928.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12928 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12928 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12928 := gPlus_lower 12928
end BstLean.Part269.N12928

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12928
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035489283177 : ℝ) ≤ wn 12928 := by
  have hn : √(12928 : ℝ) ≤ 113.701363228416 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12928 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.701363228416 ≤ 2 / √(12928 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247362235 : ℝ) ≤ rhoBar 12928 BstLean.Part154.csC ∧
    rhoBar 12928 BstLean.Part154.csC ≤ 0.000247362618 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035489283177 : ℝ) / (1.295212 * 12928) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035489283178 : ℝ) / (1.29521 * 12928) := by gcongr
      _ ≤ (0.000247362618 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12928 BstLean.Part154.csC) ≤ 0.000989511661 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12928 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12928 BstLean.Part154.csC) (piBar (rhoBar 12928 BstLean.Part154.csC)) ≤ 0.000188937079 ∧
    cc1 (rhoBar 12928 BstLean.Part154.csC) (piBar (rhoBar 12928 BstLean.Part154.csC)) ≤ 0.000120221950 ∧
    cc2 (rhoBar 12928 BstLean.Part154.csC) ≤ 0.000069789803 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12928 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12928 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12928 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12928 BstLean.Part154.csC * nuR (rhoBar 12928 BstLean.Part154.csC)) ≤ 0.000494740534 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247362618 : ℝ) * 0.000989511661 := by gcongr
      _ ≤ (0.000494740534 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12928 BstLean.Part154.csC) * nuR (rhoBar 12928 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000989511661 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12928 BstLean.Part154.csC) * rhoBar 12928 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247362618 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247362618 / 2 + 0.399 * 0.000989511661 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188937079 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494740534 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120221950 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247362618 / 1.414213562 := by gcongr
      _ ≤ (0.000069789803 : ℝ) := by norm_num

end BstLean.Part269.N12928

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12928
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12928 BstLean.Part154.csC) (piBar (rhoBar 12928 BstLean.Part154.csC)) ≤ 1.54159E-7 := by
  have hr0 : 0 ≤ rhoBar 12928 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12928 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12928 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12928 BstLean.Part154.csC) (piBar (rhoBar 12928 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12928 BstLean.Part154.csC) (piBar (rhoBar 12928 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12928 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188937079 : ℝ) ^ 2 + 0.000120221950 ^ 2 + 3 * 0.000069789803 ^ 2 +
        2 * 0.797885 * 0.000188937079 * 0.000120221950 + 2 * 0.000188937079 * 0.000069789803 +
        4 * 0.797885 * 0.000120221950 * 0.000069789803 := by gcongr
    _ ≤ (1.54159E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12928 BstLean.Part154.csC Θ ≤ 0.002581315494 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12928 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12928 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12928 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12928 BstLean.Part154.csC) (piBar (rhoBar 12928 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12928 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035489283178 * 1.54159E-7 / (0.000247362235 : ℝ) := by gcongr
    _ ≤ 0.002581315494 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12928 BstLean.Part154.csC Θ ≤ 0.002863229402 + 0.000652258702 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12928 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12928 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12928 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035489283178 : ℝ) * ((2 * Θ * 0.000247362618 +
        (6863 / 10000) * 0.000247362618 * 12928 * 0.000989511661) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002863229402 + 0.000652258702 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12928 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12928 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12928 0.011 Θ ∧ gammaRatio 12928 0.011 Θ ≤ 0.000085036872 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12928 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035489283178 : ℝ) * 0.525 / ((1 - 0.011) * 12928) := by gcongr
      _ ≤ (0.000085036872 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12928 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12928 0.011 Θ) :=
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
    badAllowance 12928 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12928 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12928 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12928 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12928 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12928 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12928 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12928 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12928 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12928 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12928 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035489283178 : ℝ) * 12928 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12928 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003283787958 + 0.003233574196 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12928

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12928
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12928 BstLean.Part154.csC) (piBar (rhoBar 12928 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12928 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12928 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12928 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12928 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12928 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12928 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12928 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12928 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12928 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12928 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12928 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12928 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12928 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12928 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052014447606 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12928) ≤ 0.010503282874 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12928 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035489283178)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010503282874 + 2 * 0.737676 / 12928) := by gcongr
    _ ≤ (0.052014447606 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12928 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12928

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12928
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513697284 : ℝ) ≤ plow 12928 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12928) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052488014411)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355190635) : eMP 12928 0.011 xi bn ≤ 0.001166991216 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12928 : ℝ) * (1 - 0.011))) ≤ 0.000577047201 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001355190635 / (12928 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577047201 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577047201 : ℝ) + 3.141593 * 0.052488014411 / (12928 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001166991216 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052488014411)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355190635) : PiBarMP 12928 12 0.011 xi bn ≤ 0.159808278128 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12928 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036812913971 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.074276473475 : ℝ) ≤ √((12928 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.701363228415 : ℝ) ≤ √(12928 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12928) ≤ 0.122535103074 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036812913971 + 0.052488014411 * 1.772454 / (2 * (113.074276473475 : ℝ))) * (1 + 0.001166991216) +
        8 / (12928 * 113.701363228415) + 0.122535103074 := by gcongr
    _ ≤ (0.159808278128 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052488014411)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355190635) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281117076162) :
    parallelOracle 12928 0.011 xi bn cd ≤ 0.160780735119 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12928 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12928 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513697284 : ℝ) ≤ plow 12928 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.701363228415 : ℝ) ≤ √(12928 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281117076162 : ℝ) / (2 * 0.560513697284 * 113.701363228415)) * 0.159808278128 +
        0.281117076162 ^ 2 / (2 * 0.560513697284 * 113.701363228415) := by gcongr
    _ ≤ (0.160780735119 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052488014411) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355190635)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281117076162) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12928 12928 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513697284 : ℝ) ≤ plow 12928 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.701363228415 : ℝ) ≤ √(12928 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12928 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12928 Θ 1.22 ≤ 0.011663013199 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.701363228415 := by gcongr <;> linarith
      _ ≤ (0.011663013199 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12928 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12928 12928 0.011 ≤ 0.008406996514 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12928 12928 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12928 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12928 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12928 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12928 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160780735119 + 0.011663013199 + (0.008406996514 : ℝ) *
        (1 + 2 * (0.281117076162 + 0.011663013199) / (0.560513697284 * 113.701363228415))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12928]

end BstLean.Part269.N12928

/-! The original eight local profiles supply actual 12928 moment certificates. -/
namespace BstLean.Part269.N12928
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12928 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12928 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12928 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052488014411 ∧
    0 ≤ bN 12928 BstLean.Part154.csC (groupTheta g) ∧ bN 12928 BstLean.Part154.csC (groupTheta g) ≤ 0.001355190635 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12928 12928 0.011
      (momentAllowance 12928 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12928 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12928 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12928 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12928 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12928 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229102628556 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12928 0.011
      (momentAllowance 12928 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12928 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12928
/-! The actual computed-centre upper energy formula at 12928. -/
namespace BstLean.Part269.N12928
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12928

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12928
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12928)
open BstLean.Part268 (cell12928)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084851496310
  | 2 => 0.085783080331
  | 3 => 0.086711268987
  | 4 => 0.087637120540
  | 5 => 0.088561925838
  | 6 => 0.089487244221
  | 7 => 0.090414943067
  | 8 => 0.091347241047
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12928 12928 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12928 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12928

/-! Actual upper energy certificates on all 43 source endpoints at 12928. -/
namespace BstLean.Part269.N12928
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12928)
open BstLean.Part268 (cell12928)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12928 (gMinus 12928) (1 - (cell12928 i).lower) ≤ 1 ∧
    energyUpper 12928 (gMinus 12928) (BstLean.Part211.gPlus 12928)
      (finiteEnergy 12928 12928 0.011) (1 - (cell12928 i).lower) ≤
      (cell12928 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨10,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨11,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨12,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨13,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨14,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨15,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨16,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨17,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨18,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨19,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨20,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨21,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨22,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨23,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨24,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨25,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨26,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨27,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨28,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨29,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨30,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨31,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨32,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨33,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨34,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨35,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨36,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨37,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨38,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨39,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨40,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨41,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨42,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨43,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨44,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨45,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨46,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨47,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨48,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨49,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨50,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨51,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12928) (by norm_num)
        (q := 1 - (cell12928 ⟨52,by decide⟩).lower)
        (by norm_num [cell12928]) (by norm_num [cell12928])
      exact ⟨E.1,E.2.trans (by norm_num [cell12928])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12928

/-! Source-cell containment and simple scalar guards at 12928. -/
namespace BstLean.Part269.N12928
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12928)
open BstLean.Part268 (cell12928)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12928 ⟨10,by decide⟩).lower ∧ (cell12928 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12928 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12928 ⟨11,by decide⟩).lower ∧ (cell12928 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12928 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12928 ⟨12,by decide⟩).lower ∧ (cell12928 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12928 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12928 ⟨13,by decide⟩).lower ∧ (cell12928 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12928 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12928 ⟨14,by decide⟩).lower ∧ (cell12928 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12928 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12928 ⟨15,by decide⟩).lower ∧ (cell12928 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12928 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12928 ⟨16,by decide⟩).lower ∧ (cell12928 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12928 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12928 ⟨17,by decide⟩).lower ∧ (cell12928 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12928 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12928 ⟨18,by decide⟩).lower ∧ (cell12928 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12928 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12928 ⟨19,by decide⟩).lower ∧ (cell12928 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12928 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12928 ⟨20,by decide⟩).lower ∧ (cell12928 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12928 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12928 ⟨21,by decide⟩).lower ∧ (cell12928 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12928 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12928 ⟨22,by decide⟩).lower ∧ (cell12928 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12928 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12928 ⟨23,by decide⟩).lower ∧ (cell12928 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12928 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12928 ⟨24,by decide⟩).lower ∧ (cell12928 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12928 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12928 ⟨25,by decide⟩).lower ∧ (cell12928 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12928 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12928 ⟨26,by decide⟩).lower ∧ (cell12928 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12928 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12928 ⟨27,by decide⟩).lower ∧ (cell12928 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12928 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12928 ⟨28,by decide⟩).lower ∧ (cell12928 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12928 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12928 ⟨29,by decide⟩).lower ∧ (cell12928 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12928 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12928 ⟨30,by decide⟩).lower ∧ (cell12928 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12928 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12928 ⟨31,by decide⟩).lower ∧ (cell12928 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12928 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12928 ⟨32,by decide⟩).lower ∧ (cell12928 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12928 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12928 ⟨33,by decide⟩).lower ∧ (cell12928 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12928 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12928 ⟨34,by decide⟩).lower ∧ (cell12928 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12928 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12928 ⟨35,by decide⟩).lower ∧ (cell12928 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12928 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12928 ⟨36,by decide⟩).lower ∧ (cell12928 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12928 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12928 ⟨37,by decide⟩).lower ∧ (cell12928 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12928 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12928 ⟨38,by decide⟩).lower ∧ (cell12928 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12928 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12928 ⟨39,by decide⟩).lower ∧ (cell12928 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12928 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12928 ⟨40,by decide⟩).lower ∧ (cell12928 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12928 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12928 ⟨41,by decide⟩).lower ∧ (cell12928 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12928 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12928 ⟨42,by decide⟩).lower ∧ (cell12928 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12928 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12928 ⟨43,by decide⟩).lower ∧ (cell12928 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12928 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12928 ⟨44,by decide⟩).lower ∧ (cell12928 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12928 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12928 ⟨45,by decide⟩).lower ∧ (cell12928 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12928 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12928 ⟨46,by decide⟩).lower ∧ (cell12928 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12928 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12928 ⟨47,by decide⟩).lower ∧ (cell12928 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12928 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12928 ⟨48,by decide⟩).lower ∧ (cell12928 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12928 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12928 ⟨49,by decide⟩).lower ∧ (cell12928 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12928 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12928 ⟨50,by decide⟩).lower ∧ (cell12928 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12928 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12928 ⟨51,by decide⟩).lower ∧ (cell12928 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12928 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12928 ⟨52,by decide⟩).lower ∧ (cell12928 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12928 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12928 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12928 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12928,cell12928,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12928 i).lower ∧
    (cell12928 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12928 i).upper ≤ (0.532 : ℝ) ∧
    (cell12928 i).centre ≤ (0.1 : ℝ) ∧ (cell12928 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12928 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12928 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12928

/-! The local source numeric instances at 12928 have no network premises. -/
namespace BstLean.Part269.N12928
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12928)
open BstLean.Part268 (cell12928)

noncomputable def sourceNumerics12928 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12928 (cell12928 i)
      scalarRow12928.M scalarRow12928.H scalarRow12928.xi := by
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
    energy_allowance := scalarRow12928.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12928]
    centre_nonneg := (scalarRow12928.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12928])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12928
/-! Actual 12929 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12929
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12929 ≤ (1.035487898718 : ℝ) := by
  have hr : (113.705760628035 : ℝ) ≤ √(12929 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.705760628035 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12929 12929 (11 / 1000) ≤
    (0.008406671384 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12929) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.705760628035 : ℝ) ≤ √(12929 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12929)
  have hdiv : K / √(12929 : ℝ) ≤ K / 113.705760628035 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.705760628035 ≤ (0.008406671384 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12929.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12929 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12929 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12929 := gPlus_lower 12929
end BstLean.Part269.N12929

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12929
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035487898717 : ℝ) ≤ wn 12929 := by
  have hn : √(12929 : ℝ) ≤ 113.705760628036 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12929 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.705760628036 ≤ 2 / √(12929 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247342772 : ℝ) ≤ rhoBar 12929 BstLean.Part154.csC ∧
    rhoBar 12929 BstLean.Part154.csC ≤ 0.000247343155 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035487898717 : ℝ) / (1.295212 * 12929) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035487898718 : ℝ) / (1.29521 * 12929) := by gcongr
      _ ≤ (0.000247343155 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12929 BstLean.Part154.csC) ≤ 0.000989433799 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12929 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12929 BstLean.Part154.csC) (piBar (rhoBar 12929 BstLean.Part154.csC)) ≤ 0.000188922212 ∧
    cc1 (rhoBar 12929 BstLean.Part154.csC) (piBar (rhoBar 12929 BstLean.Part154.csC)) ≤ 0.000120212491 ∧
    cc2 (rhoBar 12929 BstLean.Part154.csC) ≤ 0.000069784311 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12929 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12929 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12929 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12929 BstLean.Part154.csC * nuR (rhoBar 12929 BstLean.Part154.csC)) ≤ 0.000494701605 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247343155 : ℝ) * 0.000989433799 := by gcongr
      _ ≤ (0.000494701605 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12929 BstLean.Part154.csC) * nuR (rhoBar 12929 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000989433799 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12929 BstLean.Part154.csC) * rhoBar 12929 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247343155 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247343155 / 2 + 0.399 * 0.000989433799 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188922212 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494701605 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120212491 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247343155 / 1.414213562 := by gcongr
      _ ≤ (0.000069784311 : ℝ) := by norm_num

end BstLean.Part269.N12929

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12929
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12929 BstLean.Part154.csC) (piBar (rhoBar 12929 BstLean.Part154.csC)) ≤ 1.54135E-7 := by
  have hr0 : 0 ≤ rhoBar 12929 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12929 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12929 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12929 BstLean.Part154.csC) (piBar (rhoBar 12929 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12929 BstLean.Part154.csC) (piBar (rhoBar 12929 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12929 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188922212 : ℝ) ^ 2 + 0.000120212491 ^ 2 + 3 * 0.000069784311 ^ 2 +
        2 * 0.797885 * 0.000188922212 * 0.000120212491 + 2 * 0.000188922212 * 0.000069784311 +
        4 * 0.797885 * 0.000120212491 * 0.000069784311 := by gcongr
    _ ≤ (1.54135E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12929 BstLean.Part154.csC Θ ≤ 0.002581113263 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12929 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12929 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12929 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12929 BstLean.Part154.csC) (piBar (rhoBar 12929 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12929 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035487898718 * 1.54135E-7 / (0.000247342772 : ℝ) := by gcongr
    _ ≤ 0.002581113263 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12929 BstLean.Part154.csC Θ ≤ 0.002862996448 + 0.000652206509 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12929 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12929 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12929 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035487898718 : ℝ) * ((2 * Θ * 0.000247343155 +
        (6863 / 10000) * 0.000247343155 * 12929 * 0.000989433799) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002862996448 + 0.000652206509 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12929 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12929 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12929 0.011 Θ ∧ gammaRatio 12929 0.011 Θ ≤ 0.000085030181 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12929 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035487898718 : ℝ) * 0.525 / ((1 - 0.011) * 12929) := by gcongr
      _ ≤ (0.000085030181 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12929 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12929 0.011 Θ) :=
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
    badAllowance 12929 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12929 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12929 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12929 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12929 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12929 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12929 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12929 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12929 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12929 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12929 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035487898718 : ℝ) * 12929 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12929 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003283555004 + 0.003233319772 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12929

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12929
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12929 BstLean.Part154.csC) (piBar (rhoBar 12929 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12929 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12929 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12929 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12929 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12929 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12929 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12929 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12929 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12929 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12929 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12929 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12929 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12929 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12929 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052012414404 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12929) ≤ 0.010502876675 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12929 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035487898718)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010502876675 + 2 * 0.737676 / 12929) := by gcongr
    _ ≤ (0.052012414404 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12929 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12929

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12929
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513740923 : ℝ) ≤ plow 12929 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12929) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052487647885)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355084464) : eMP 12929 0.011 xi bn ≤ 0.001166900289 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12929 : ℝ) * (1 - 0.011))) ≤ 0.000577002281 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001355084464 / (12929 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000577002281 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000577002281 : ℝ) + 3.141593 * 0.052487647885 / (12929 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001166900289 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052487647885)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355084464) : PiBarMP 12929 12 0.011 xi bn ≤ 0.159802072700 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12929 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036811471908 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.078649620518 : ℝ) ≤ √((12929 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.705760628035 : ℝ) ≤ √(12929 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12929) ≤ 0.122530364212 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036811471908 + 0.052487647885 * 1.772454 / (2 * (113.078649620518 : ℝ))) * (1 + 0.001166900289) +
        8 / (12929 * 113.705760628035) + 0.122530364212 := by gcongr
    _ ≤ (0.159802072700 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052487647885)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355084464) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281114243042) :
    parallelOracle 12929 0.011 xi bn cd ≤ 0.160774462273 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12929 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12929 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513740923 : ℝ) ≤ plow 12929 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.705760628035 : ℝ) ≤ √(12929 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281114243042 : ℝ) / (2 * 0.560513740923 * 113.705760628035)) * 0.159802072700 +
        0.281114243042 ^ 2 / (2 * 0.560513740923 * 113.705760628035) := by gcongr
    _ ≤ (0.160774462273 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052487647885) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001355084464)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281114243042) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12929 12929 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513740923 : ℝ) ≤ plow 12929 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.705760628035 : ℝ) ≤ √(12929 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12929 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12929 Θ 1.22 ≤ 0.011662562149 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.705760628035 := by gcongr <;> linarith
      _ ≤ (0.011662562149 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12929 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12929 12929 0.011 ≤ 0.008406671384 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12929 12929 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12929 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12929 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12929 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12929 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160774462273 + 0.011662562149 + (0.008406671384 : ℝ) *
        (1 + 2 * (0.281114243042 + 0.011662562149) / (0.560513740923 * 113.705760628035))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12929]

end BstLean.Part269.N12929

/-! The original eight local profiles supply actual 12929 moment certificates. -/
namespace BstLean.Part269.N12929
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12929 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12929 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12929 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052487647885 ∧
    0 ≤ bN 12929 BstLean.Part154.csC (groupTheta g) ∧ bN 12929 BstLean.Part154.csC (groupTheta g) ≤ 0.001355084464 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12929 12929 0.011
      (momentAllowance 12929 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12929 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12929 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12929 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12929 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12929 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229101828638 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12929 0.011
      (momentAllowance 12929 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12929 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12929
/-! The actual computed-centre upper energy formula at 12929. -/
namespace BstLean.Part269.N12929
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12929

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12929
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12929)
open BstLean.Part268 (cell12929)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084848801648
  | 2 => 0.085780340893
  | 3 => 0.086708479029
  | 4 => 0.087634272943
  | 5 => 0.088559011857
  | 6 => 0.089484253207
  | 7 => 0.090411862141
  | 8 => 0.091344054747
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12929 12929 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12929 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12929

/-! Actual upper energy certificates on all 43 source endpoints at 12929. -/
namespace BstLean.Part269.N12929
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12929)
open BstLean.Part268 (cell12929)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12929 (gMinus 12929) (1 - (cell12929 i).lower) ≤ 1 ∧
    energyUpper 12929 (gMinus 12929) (BstLean.Part211.gPlus 12929)
      (finiteEnergy 12929 12929 0.011) (1 - (cell12929 i).lower) ≤
      (cell12929 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨10,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨11,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨12,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨13,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨14,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨15,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨16,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨17,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨18,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨19,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨20,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨21,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨22,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨23,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨24,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨25,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨26,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨27,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨28,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨29,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨30,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨31,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨32,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨33,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨34,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨35,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨36,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨37,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨38,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨39,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨40,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨41,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨42,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨43,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨44,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨45,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨46,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨47,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨48,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨49,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨50,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨51,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12929) (by norm_num)
        (q := 1 - (cell12929 ⟨52,by decide⟩).lower)
        (by norm_num [cell12929]) (by norm_num [cell12929])
      exact ⟨E.1,E.2.trans (by norm_num [cell12929])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12929

/-! Source-cell containment and simple scalar guards at 12929. -/
namespace BstLean.Part269.N12929
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12929)
open BstLean.Part268 (cell12929)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12929 ⟨10,by decide⟩).lower ∧ (cell12929 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12929 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12929 ⟨11,by decide⟩).lower ∧ (cell12929 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12929 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12929 ⟨12,by decide⟩).lower ∧ (cell12929 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12929 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12929 ⟨13,by decide⟩).lower ∧ (cell12929 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12929 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12929 ⟨14,by decide⟩).lower ∧ (cell12929 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12929 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12929 ⟨15,by decide⟩).lower ∧ (cell12929 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12929 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12929 ⟨16,by decide⟩).lower ∧ (cell12929 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12929 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12929 ⟨17,by decide⟩).lower ∧ (cell12929 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12929 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12929 ⟨18,by decide⟩).lower ∧ (cell12929 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12929 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12929 ⟨19,by decide⟩).lower ∧ (cell12929 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12929 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12929 ⟨20,by decide⟩).lower ∧ (cell12929 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12929 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12929 ⟨21,by decide⟩).lower ∧ (cell12929 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12929 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12929 ⟨22,by decide⟩).lower ∧ (cell12929 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12929 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12929 ⟨23,by decide⟩).lower ∧ (cell12929 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12929 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12929 ⟨24,by decide⟩).lower ∧ (cell12929 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12929 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12929 ⟨25,by decide⟩).lower ∧ (cell12929 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12929 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12929 ⟨26,by decide⟩).lower ∧ (cell12929 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12929 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12929 ⟨27,by decide⟩).lower ∧ (cell12929 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12929 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12929 ⟨28,by decide⟩).lower ∧ (cell12929 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12929 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12929 ⟨29,by decide⟩).lower ∧ (cell12929 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12929 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12929 ⟨30,by decide⟩).lower ∧ (cell12929 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12929 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12929 ⟨31,by decide⟩).lower ∧ (cell12929 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12929 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12929 ⟨32,by decide⟩).lower ∧ (cell12929 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12929 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12929 ⟨33,by decide⟩).lower ∧ (cell12929 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12929 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12929 ⟨34,by decide⟩).lower ∧ (cell12929 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12929 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12929 ⟨35,by decide⟩).lower ∧ (cell12929 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12929 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12929 ⟨36,by decide⟩).lower ∧ (cell12929 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12929 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12929 ⟨37,by decide⟩).lower ∧ (cell12929 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12929 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12929 ⟨38,by decide⟩).lower ∧ (cell12929 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12929 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12929 ⟨39,by decide⟩).lower ∧ (cell12929 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12929 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12929 ⟨40,by decide⟩).lower ∧ (cell12929 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12929 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12929 ⟨41,by decide⟩).lower ∧ (cell12929 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12929 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12929 ⟨42,by decide⟩).lower ∧ (cell12929 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12929 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12929 ⟨43,by decide⟩).lower ∧ (cell12929 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12929 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12929 ⟨44,by decide⟩).lower ∧ (cell12929 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12929 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12929 ⟨45,by decide⟩).lower ∧ (cell12929 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12929 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12929 ⟨46,by decide⟩).lower ∧ (cell12929 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12929 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12929 ⟨47,by decide⟩).lower ∧ (cell12929 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12929 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12929 ⟨48,by decide⟩).lower ∧ (cell12929 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12929 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12929 ⟨49,by decide⟩).lower ∧ (cell12929 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12929 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12929 ⟨50,by decide⟩).lower ∧ (cell12929 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12929 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12929 ⟨51,by decide⟩).lower ∧ (cell12929 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12929 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12929 ⟨52,by decide⟩).lower ∧ (cell12929 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12929 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12929 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12929 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12929,cell12929,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12929 i).lower ∧
    (cell12929 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12929 i).upper ≤ (0.532 : ℝ) ∧
    (cell12929 i).centre ≤ (0.1 : ℝ) ∧ (cell12929 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12929 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12929 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12929

/-! The local source numeric instances at 12929 have no network premises. -/
namespace BstLean.Part269.N12929
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12929)
open BstLean.Part268 (cell12929)

noncomputable def sourceNumerics12929 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12929 (cell12929 i)
      scalarRow12929.M scalarRow12929.H scalarRow12929.xi := by
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
    energy_allowance := scalarRow12929.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12929]
    centre_nonneg := (scalarRow12929.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12929])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12929
/-! Actual 12930 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12930
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12930 ≤ (1.035486514419 : ℝ) := by
  have hr : (113.710157857598 : ℝ) ≤ √(12930 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.710157857598 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12930 12930 (11 / 1000) ≤
    (0.008406346291 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12930) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.710157857598 : ℝ) ≤ √(12930 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12930)
  have hdiv : K / √(12930 : ℝ) ≤ K / 113.710157857598 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.710157857598 ≤ (0.008406346291 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12930.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12930 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12930 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12930 := gPlus_lower 12930
end BstLean.Part269.N12930

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12930
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035486514418 : ℝ) ≤ wn 12930 := by
  have hn : √(12930 : ℝ) ≤ 113.710157857599 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12930 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.710157857599 ≤ 2 / √(12930 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247323312 : ℝ) ≤ rhoBar 12930 BstLean.Part154.csC ∧
    rhoBar 12930 BstLean.Part154.csC ≤ 0.000247323695 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035486514418 : ℝ) / (1.295212 * 12930) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035486514419 : ℝ) / (1.29521 * 12930) := by gcongr
      _ ≤ (0.000247323695 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12930 BstLean.Part154.csC) ≤ 0.000989355950 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12930 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12930 BstLean.Part154.csC) (piBar (rhoBar 12930 BstLean.Part154.csC)) ≤ 0.000188907348 ∧
    cc1 (rhoBar 12930 BstLean.Part154.csC) (piBar (rhoBar 12930 BstLean.Part154.csC)) ≤ 0.000120203032 ∧
    cc2 (rhoBar 12930 BstLean.Part154.csC) ≤ 0.000069778821 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12930 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12930 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12930 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12930 BstLean.Part154.csC * nuR (rhoBar 12930 BstLean.Part154.csC)) ≤ 0.000494662683 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247323695 : ℝ) * 0.000989355950 := by gcongr
      _ ≤ (0.000494662683 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12930 BstLean.Part154.csC) * nuR (rhoBar 12930 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000989355950 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12930 BstLean.Part154.csC) * rhoBar 12930 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247323695 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247323695 / 2 + 0.399 * 0.000989355950 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188907348 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494662683 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120203032 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247323695 / 1.414213562 := by gcongr
      _ ≤ (0.000069778821 : ℝ) := by norm_num

end BstLean.Part269.N12930

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12930
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12930 BstLean.Part154.csC) (piBar (rhoBar 12930 BstLean.Part154.csC)) ≤ 1.54111E-7 := by
  have hr0 : 0 ≤ rhoBar 12930 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12930 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12930 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12930 BstLean.Part154.csC) (piBar (rhoBar 12930 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12930 BstLean.Part154.csC) (piBar (rhoBar 12930 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12930 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188907348 : ℝ) ^ 2 + 0.000120203032 ^ 2 + 3 * 0.000069778821 ^ 2 +
        2 * 0.797885 * 0.000188907348 * 0.000120203032 + 2 * 0.000188907348 * 0.000069778821 +
        4 * 0.797885 * 0.000120203032 * 0.000069778821 := by gcongr
    _ ≤ (1.54111E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12930 BstLean.Part154.csC Θ ≤ 0.002580910970 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12930 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12930 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12930 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12930 BstLean.Part154.csC) (piBar (rhoBar 12930 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12930 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035486514419 * 1.54111E-7 / (0.000247323312 : ℝ) := by gcongr
    _ ≤ 0.002580910970 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12930 BstLean.Part154.csC Θ ≤ 0.002862763532 + 0.000652154324 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12930 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12930 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12930 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035486514419 : ℝ) * ((2 * Θ * 0.000247323695 +
        (6863 / 10000) * 0.000247323695 * 12930 * 0.000989355950) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002862763532 + 0.000652154324 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12930 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12930 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12930 0.011 Θ ∧ gammaRatio 12930 0.011 Θ ≤ 0.000085023491 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12930 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035486514419 : ℝ) * 0.525 / ((1 - 0.011) * 12930) := by gcongr
      _ ≤ (0.000085023491 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12930 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12930 0.011 Θ) :=
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
    badAllowance 12930 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12930 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12930 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12930 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12930 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12930 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12930 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12930 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12930 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12930 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12930 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035486514419 : ℝ) * 12930 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12930 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003283322088 + 0.003233065294 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12930

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12930
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12930 BstLean.Part154.csC) (piBar (rhoBar 12930 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12930 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12930 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12930 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12930 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12930 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12930 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12930 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12930 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12930 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12930 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12930 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12930 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12930 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12930 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052010381438 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12930) ≤ 0.010502470523 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12930 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035486514419)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010502470523 + 2 * 0.737676 / 12930) := by gcongr
    _ ≤ (0.052010381438 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12930 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12930

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12930
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513784555 : ℝ) ≤ plow 12930 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12930) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052487281368)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354978260) : eMP 12930 0.011 xi bn ≤ 0.001166809355 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12930 : ℝ) * (1 - 0.011))) ≤ 0.000576957358 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001354978260 / (12930 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576957358 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576957358 : ℝ) + 3.141593 * 0.052487281368 / (12930 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001166809355 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052487281368)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354978260) : PiBarMP 12930 12 0.011 xi bn ≤ 0.159795867320 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12930 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036810029340 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.083022598443 : ℝ) ≤ √((12930 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.710157857598 : ℝ) ≤ √(12930 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12930) ≤ 0.122525625901 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036810029340 + 0.052487281368 * 1.772454 / (2 * (113.083022598443 : ℝ))) * (1 + 0.001166809355) +
        8 / (12930 * 113.710157857598) + 0.122525625901 := by gcongr
    _ ≤ (0.159795867320 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052487281368)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354978260) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281111410175) :
    parallelOracle 12930 0.011 xi bn cd ≤ 0.160768189484 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12930 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12930 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513784555 : ℝ) ≤ plow 12930 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.710157857598 : ℝ) ≤ √(12930 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281111410175 : ℝ) / (2 * 0.560513784555 * 113.710157857598)) * 0.159795867320 +
        0.281111410175 ^ 2 / (2 * 0.560513784555 * 113.710157857598) := by gcongr
    _ ≤ (0.160768189484 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052487281368) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354978260)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281111410175) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12930 12930 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513784555 : ℝ) ≤ plow 12930 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.710157857598 : ℝ) ≤ √(12930 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12930 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12930 Θ 1.22 ≤ 0.011662111152 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.710157857598 := by gcongr <;> linarith
      _ ≤ (0.011662111152 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12930 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12930 12930 0.011 ≤ 0.008406346291 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12930 12930 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12930 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12930 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12930 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12930 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160768189484 + 0.011662111152 + (0.008406346291 : ℝ) *
        (1 + 2 * (0.281111410175 + 0.011662111152) / (0.560513784555 * 113.710157857598))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12930]

end BstLean.Part269.N12930

/-! The original eight local profiles supply actual 12930 moment certificates. -/
namespace BstLean.Part269.N12930
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12930 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12930 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12930 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052487281368 ∧
    0 ≤ bN 12930 BstLean.Part154.csC (groupTheta g) ∧ bN 12930 BstLean.Part154.csC (groupTheta g) ≤ 0.001354978260 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12930 12930 0.011
      (momentAllowance 12930 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12930 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12930 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12930 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12930 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12930 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229101028737 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12930 0.011
      (momentAllowance 12930 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12930 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12930
/-! The actual computed-centre upper energy formula at 12930. -/
namespace BstLean.Part269.N12930
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12930

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12930
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12930)
open BstLean.Part268 (cell12930)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084846107851
  | 2 => 0.085777602355
  | 3 => 0.086705690012
  | 4 => 0.087631426336
  | 5 => 0.088556098929
  | 6 => 0.089481263320
  | 7 => 0.090408782433
  | 8 => 0.091340869776
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12930 12930 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12930 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12930

/-! Actual upper energy certificates on all 43 source endpoints at 12930. -/
namespace BstLean.Part269.N12930
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12930)
open BstLean.Part268 (cell12930)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12930 (gMinus 12930) (1 - (cell12930 i).lower) ≤ 1 ∧
    energyUpper 12930 (gMinus 12930) (BstLean.Part211.gPlus 12930)
      (finiteEnergy 12930 12930 0.011) (1 - (cell12930 i).lower) ≤
      (cell12930 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨10,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨11,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨12,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨13,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨14,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨15,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨16,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨17,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨18,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨19,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨20,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨21,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨22,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨23,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨24,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨25,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨26,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨27,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨28,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨29,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨30,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨31,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨32,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨33,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨34,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨35,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨36,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨37,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨38,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨39,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨40,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨41,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨42,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨43,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨44,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨45,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨46,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨47,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨48,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨49,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨50,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨51,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12930) (by norm_num)
        (q := 1 - (cell12930 ⟨52,by decide⟩).lower)
        (by norm_num [cell12930]) (by norm_num [cell12930])
      exact ⟨E.1,E.2.trans (by norm_num [cell12930])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12930

/-! Source-cell containment and simple scalar guards at 12930. -/
namespace BstLean.Part269.N12930
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12930)
open BstLean.Part268 (cell12930)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12930 ⟨10,by decide⟩).lower ∧ (cell12930 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12930 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12930 ⟨11,by decide⟩).lower ∧ (cell12930 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12930 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12930 ⟨12,by decide⟩).lower ∧ (cell12930 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12930 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12930 ⟨13,by decide⟩).lower ∧ (cell12930 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12930 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12930 ⟨14,by decide⟩).lower ∧ (cell12930 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12930 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12930 ⟨15,by decide⟩).lower ∧ (cell12930 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12930 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12930 ⟨16,by decide⟩).lower ∧ (cell12930 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12930 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12930 ⟨17,by decide⟩).lower ∧ (cell12930 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12930 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12930 ⟨18,by decide⟩).lower ∧ (cell12930 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12930 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12930 ⟨19,by decide⟩).lower ∧ (cell12930 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12930 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12930 ⟨20,by decide⟩).lower ∧ (cell12930 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12930 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12930 ⟨21,by decide⟩).lower ∧ (cell12930 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12930 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12930 ⟨22,by decide⟩).lower ∧ (cell12930 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12930 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12930 ⟨23,by decide⟩).lower ∧ (cell12930 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12930 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12930 ⟨24,by decide⟩).lower ∧ (cell12930 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12930 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12930 ⟨25,by decide⟩).lower ∧ (cell12930 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12930 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12930 ⟨26,by decide⟩).lower ∧ (cell12930 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12930 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12930 ⟨27,by decide⟩).lower ∧ (cell12930 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12930 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12930 ⟨28,by decide⟩).lower ∧ (cell12930 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12930 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12930 ⟨29,by decide⟩).lower ∧ (cell12930 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12930 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12930 ⟨30,by decide⟩).lower ∧ (cell12930 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12930 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12930 ⟨31,by decide⟩).lower ∧ (cell12930 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12930 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12930 ⟨32,by decide⟩).lower ∧ (cell12930 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12930 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12930 ⟨33,by decide⟩).lower ∧ (cell12930 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12930 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12930 ⟨34,by decide⟩).lower ∧ (cell12930 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12930 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12930 ⟨35,by decide⟩).lower ∧ (cell12930 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12930 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12930 ⟨36,by decide⟩).lower ∧ (cell12930 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12930 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12930 ⟨37,by decide⟩).lower ∧ (cell12930 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12930 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12930 ⟨38,by decide⟩).lower ∧ (cell12930 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12930 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12930 ⟨39,by decide⟩).lower ∧ (cell12930 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12930 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12930 ⟨40,by decide⟩).lower ∧ (cell12930 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12930 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12930 ⟨41,by decide⟩).lower ∧ (cell12930 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12930 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12930 ⟨42,by decide⟩).lower ∧ (cell12930 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12930 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12930 ⟨43,by decide⟩).lower ∧ (cell12930 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12930 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12930 ⟨44,by decide⟩).lower ∧ (cell12930 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12930 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12930 ⟨45,by decide⟩).lower ∧ (cell12930 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12930 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12930 ⟨46,by decide⟩).lower ∧ (cell12930 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12930 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12930 ⟨47,by decide⟩).lower ∧ (cell12930 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12930 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12930 ⟨48,by decide⟩).lower ∧ (cell12930 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12930 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12930 ⟨49,by decide⟩).lower ∧ (cell12930 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12930 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12930 ⟨50,by decide⟩).lower ∧ (cell12930 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12930 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12930 ⟨51,by decide⟩).lower ∧ (cell12930 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12930 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12930 ⟨52,by decide⟩).lower ∧ (cell12930 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12930 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12930 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12930 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12930,cell12930,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12930 i).lower ∧
    (cell12930 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12930 i).upper ≤ (0.532 : ℝ) ∧
    (cell12930 i).centre ≤ (0.1 : ℝ) ∧ (cell12930 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12930 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12930 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12930

/-! The local source numeric instances at 12930 have no network premises. -/
namespace BstLean.Part269.N12930
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12930)
open BstLean.Part268 (cell12930)

noncomputable def sourceNumerics12930 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12930 (cell12930 i)
      scalarRow12930.M scalarRow12930.H scalarRow12930.xi := by
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
    energy_allowance := scalarRow12930.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12930]
    centre_nonneg := (scalarRow12930.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12930])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12930
/-! Actual 12931 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12931
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12931 ≤ (1.035485130282 : ℝ) := by
  have hr : (113.714554917125 : ℝ) ≤ √(12931 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.714554917125 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12931 12931 (11 / 1000) ≤
    (0.008406021236 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12931) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.714554917125 : ℝ) ≤ √(12931 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12931)
  have hdiv : K / √(12931 : ℝ) ≤ K / 113.714554917125 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.714554917125 ≤ (0.008406021236 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12931.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12931 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12931 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12931 := gPlus_lower 12931
end BstLean.Part269.N12931

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12931
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035485130281 : ℝ) ≤ wn 12931 := by
  have hn : √(12931 : ℝ) ≤ 113.714554917126 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12931 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.714554917126 ≤ 2 / √(12931 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247303855 : ℝ) ≤ rhoBar 12931 BstLean.Part154.csC ∧
    rhoBar 12931 BstLean.Part154.csC ≤ 0.000247304238 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035485130281 : ℝ) / (1.295212 * 12931) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035485130282 : ℝ) / (1.29521 * 12931) := by gcongr
      _ ≤ (0.000247304238 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12931 BstLean.Part154.csC) ≤ 0.000989278112 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12931 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12931 BstLean.Part154.csC) (piBar (rhoBar 12931 BstLean.Part154.csC)) ≤ 0.000188892486 ∧
    cc1 (rhoBar 12931 BstLean.Part154.csC) (piBar (rhoBar 12931 BstLean.Part154.csC)) ≤ 0.000120193576 ∧
    cc2 (rhoBar 12931 BstLean.Part154.csC) ≤ 0.000069773331 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12931 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12931 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12931 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12931 BstLean.Part154.csC * nuR (rhoBar 12931 BstLean.Part154.csC)) ≤ 0.000494623766 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247304238 : ℝ) * 0.000989278112 := by gcongr
      _ ≤ (0.000494623766 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12931 BstLean.Part154.csC) * nuR (rhoBar 12931 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000989278112 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12931 BstLean.Part154.csC) * rhoBar 12931 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247304238 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247304238 / 2 + 0.399 * 0.000989278112 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188892486 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494623766 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120193576 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247304238 / 1.414213562 := by gcongr
      _ ≤ (0.000069773331 : ℝ) := by norm_num

end BstLean.Part269.N12931

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12931
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12931 BstLean.Part154.csC) (piBar (rhoBar 12931 BstLean.Part154.csC)) ≤ 1.54087E-7 := by
  have hr0 : 0 ≤ rhoBar 12931 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12931 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12931 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12931 BstLean.Part154.csC) (piBar (rhoBar 12931 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12931 BstLean.Part154.csC) (piBar (rhoBar 12931 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12931 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188892486 : ℝ) ^ 2 + 0.000120193576 ^ 2 + 3 * 0.000069773331 ^ 2 +
        2 * 0.797885 * 0.000188892486 * 0.000120193576 + 2 * 0.000188892486 * 0.000069773331 +
        4 * 0.797885 * 0.000120193576 * 0.000069773331 := by gcongr
    _ ≤ (1.54087E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12931 BstLean.Part154.csC Θ ≤ 0.002580708615 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12931 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12931 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12931 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12931 BstLean.Part154.csC) (piBar (rhoBar 12931 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12931 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035485130282 * 1.54087E-7 / (0.000247303855 : ℝ) := by gcongr
    _ ≤ 0.002580708615 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12931 BstLean.Part154.csC Θ ≤ 0.002862530650 + 0.000652102148 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12931 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12931 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12931 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035485130282 : ℝ) * ((2 * Θ * 0.000247304238 +
        (6863 / 10000) * 0.000247304238 * 12931 * 0.000989278112) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002862530650 + 0.000652102148 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12931 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12931 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12931 0.011 Θ ∧ gammaRatio 12931 0.011 Θ ≤ 0.000085016802 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12931 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035485130282 : ℝ) * 0.525 / ((1 - 0.011) * 12931) := by gcongr
      _ ≤ (0.000085016802 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12931 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12931 0.011 Θ) :=
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
    badAllowance 12931 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12931 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12931 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12931 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12931 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12931 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12931 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12931 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12931 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12931 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12931 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035485130282 : ℝ) * 12931 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12931 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003283089206 + 0.003232810763 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12931

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12931
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12931 BstLean.Part154.csC) (piBar (rhoBar 12931 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12931 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12931 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12931 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12931 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12931 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12931 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12931 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12931 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12931 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12931 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12931 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12931 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12931 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12931 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052008348714 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12931) ≤ 0.010502064419 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12931 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035485130282)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010502064419 + 2 * 0.737676 / 12931) := by gcongr
    _ ≤ (0.052008348714 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12931 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12931

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12931
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513828180 : ℝ) ≤ plow 12931 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12931) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052486914857)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354872023) : eMP 12931 0.011 xi bn ≤ 0.001166718412 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12931 : ℝ) * (1 - 0.011))) ≤ 0.000576912430 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001354872023 / (12931 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576912430 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576912430 : ℝ) + 3.141593 * 0.052486914857 / (12931 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001166718412 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052486914857)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354872023) : PiBarMP 12931 12 0.011 xi bn ≤ 0.159789661986 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12931 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036808586268 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.087395407268 : ℝ) ≤ √((12931 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.714554917125 : ℝ) ≤ √(12931 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12931) ≤ 0.122520888139 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036808586268 + 0.052486914857 * 1.772454 / (2 * (113.087395407268 : ℝ))) * (1 + 0.001166718412) +
        8 / (12931 * 113.714554917125) + 0.122520888139 := by gcongr
    _ ≤ (0.159789661986 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052486914857)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354872023) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281108577560) :
    parallelOracle 12931 0.011 xi bn cd ≤ 0.160761916750 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12931 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12931 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513828180 : ℝ) ≤ plow 12931 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.714554917125 : ℝ) ≤ √(12931 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281108577560 : ℝ) / (2 * 0.560513828180 * 113.714554917125)) * 0.159789661986 +
        0.281108577560 ^ 2 / (2 * 0.560513828180 * 113.714554917125) := by gcongr
    _ ≤ (0.160761916750 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052486914857) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354872023)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281108577560) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12931 12931 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513828180 : ℝ) ≤ plow 12931 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.714554917125 : ℝ) ≤ √(12931 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12931 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12931 Θ 1.22 ≤ 0.011661660207 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.714554917125 := by gcongr <;> linarith
      _ ≤ (0.011661660207 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12931 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12931 12931 0.011 ≤ 0.008406021236 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12931 12931 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12931 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12931 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12931 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12931 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160761916750 + 0.011661660207 + (0.008406021236 : ℝ) *
        (1 + 2 * (0.281108577560 + 0.011661660207) / (0.560513828180 * 113.714554917125))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12931]

end BstLean.Part269.N12931

/-! The original eight local profiles supply actual 12931 moment certificates. -/
namespace BstLean.Part269.N12931
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12931 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12931 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12931 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052486914857 ∧
    0 ≤ bN 12931 BstLean.Part154.csC (groupTheta g) ∧ bN 12931 BstLean.Part154.csC (groupTheta g) ≤ 0.001354872023 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12931 12931 0.011
      (momentAllowance 12931 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12931 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12931 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12931 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12931 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12931 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229100228846 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12931 0.011
      (momentAllowance 12931 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12931 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12931
/-! The actual computed-centre upper energy formula at 12931. -/
namespace BstLean.Part269.N12931
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12931

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12931
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12931)
open BstLean.Part268 (cell12931)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084843414920
  | 2 => 0.085774864716
  | 3 => 0.086702901933
  | 4 => 0.087628580718
  | 5 => 0.088553187052
  | 6 => 0.089478274559
  | 7 => 0.090405703942
  | 8 => 0.091337686132
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12931 12931 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12931 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12931

/-! Actual upper energy certificates on all 43 source endpoints at 12931. -/
namespace BstLean.Part269.N12931
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12931)
open BstLean.Part268 (cell12931)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12931 (gMinus 12931) (1 - (cell12931 i).lower) ≤ 1 ∧
    energyUpper 12931 (gMinus 12931) (BstLean.Part211.gPlus 12931)
      (finiteEnergy 12931 12931 0.011) (1 - (cell12931 i).lower) ≤
      (cell12931 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨10,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨11,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨12,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨13,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨14,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨15,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨16,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨17,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨18,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨19,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨20,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨21,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨22,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨23,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨24,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨25,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨26,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨27,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨28,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨29,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨30,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨31,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨32,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨33,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨34,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨35,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨36,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨37,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨38,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨39,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨40,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨41,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨42,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨43,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨44,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨45,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨46,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨47,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨48,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨49,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨50,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨51,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12931) (by norm_num)
        (q := 1 - (cell12931 ⟨52,by decide⟩).lower)
        (by norm_num [cell12931]) (by norm_num [cell12931])
      exact ⟨E.1,E.2.trans (by norm_num [cell12931])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12931

/-! Source-cell containment and simple scalar guards at 12931. -/
namespace BstLean.Part269.N12931
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12931)
open BstLean.Part268 (cell12931)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12931 ⟨10,by decide⟩).lower ∧ (cell12931 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12931 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12931 ⟨11,by decide⟩).lower ∧ (cell12931 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12931 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12931 ⟨12,by decide⟩).lower ∧ (cell12931 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12931 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12931 ⟨13,by decide⟩).lower ∧ (cell12931 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12931 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12931 ⟨14,by decide⟩).lower ∧ (cell12931 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12931 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12931 ⟨15,by decide⟩).lower ∧ (cell12931 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12931 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12931 ⟨16,by decide⟩).lower ∧ (cell12931 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12931 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12931 ⟨17,by decide⟩).lower ∧ (cell12931 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12931 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12931 ⟨18,by decide⟩).lower ∧ (cell12931 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12931 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12931 ⟨19,by decide⟩).lower ∧ (cell12931 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12931 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12931 ⟨20,by decide⟩).lower ∧ (cell12931 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12931 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12931 ⟨21,by decide⟩).lower ∧ (cell12931 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12931 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12931 ⟨22,by decide⟩).lower ∧ (cell12931 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12931 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12931 ⟨23,by decide⟩).lower ∧ (cell12931 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12931 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12931 ⟨24,by decide⟩).lower ∧ (cell12931 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12931 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12931 ⟨25,by decide⟩).lower ∧ (cell12931 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12931 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12931 ⟨26,by decide⟩).lower ∧ (cell12931 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12931 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12931 ⟨27,by decide⟩).lower ∧ (cell12931 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12931 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12931 ⟨28,by decide⟩).lower ∧ (cell12931 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12931 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12931 ⟨29,by decide⟩).lower ∧ (cell12931 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12931 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12931 ⟨30,by decide⟩).lower ∧ (cell12931 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12931 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12931 ⟨31,by decide⟩).lower ∧ (cell12931 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12931 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12931 ⟨32,by decide⟩).lower ∧ (cell12931 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12931 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12931 ⟨33,by decide⟩).lower ∧ (cell12931 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12931 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12931 ⟨34,by decide⟩).lower ∧ (cell12931 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12931 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12931 ⟨35,by decide⟩).lower ∧ (cell12931 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12931 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12931 ⟨36,by decide⟩).lower ∧ (cell12931 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12931 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12931 ⟨37,by decide⟩).lower ∧ (cell12931 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12931 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12931 ⟨38,by decide⟩).lower ∧ (cell12931 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12931 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12931 ⟨39,by decide⟩).lower ∧ (cell12931 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12931 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12931 ⟨40,by decide⟩).lower ∧ (cell12931 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12931 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12931 ⟨41,by decide⟩).lower ∧ (cell12931 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12931 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12931 ⟨42,by decide⟩).lower ∧ (cell12931 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12931 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12931 ⟨43,by decide⟩).lower ∧ (cell12931 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12931 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12931 ⟨44,by decide⟩).lower ∧ (cell12931 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12931 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12931 ⟨45,by decide⟩).lower ∧ (cell12931 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12931 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12931 ⟨46,by decide⟩).lower ∧ (cell12931 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12931 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12931 ⟨47,by decide⟩).lower ∧ (cell12931 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12931 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12931 ⟨48,by decide⟩).lower ∧ (cell12931 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12931 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12931 ⟨49,by decide⟩).lower ∧ (cell12931 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12931 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12931 ⟨50,by decide⟩).lower ∧ (cell12931 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12931 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12931 ⟨51,by decide⟩).lower ∧ (cell12931 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12931 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12931 ⟨52,by decide⟩).lower ∧ (cell12931 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12931 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12931 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12931 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12931,cell12931,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12931 i).lower ∧
    (cell12931 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12931 i).upper ≤ (0.532 : ℝ) ∧
    (cell12931 i).centre ≤ (0.1 : ℝ) ∧ (cell12931 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12931 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12931 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12931

/-! The local source numeric instances at 12931 have no network premises. -/
namespace BstLean.Part269.N12931
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12931)
open BstLean.Part268 (cell12931)

noncomputable def sourceNumerics12931 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12931 (cell12931 i)
      scalarRow12931.M scalarRow12931.H scalarRow12931.xi := by
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
    energy_allowance := scalarRow12931.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12931]
    centre_nonneg := (scalarRow12931.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12931])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12931
/-! Actual 12932 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12932
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12932 ≤ (1.035483746306 : ℝ) := by
  have hr : (113.718951806635 : ℝ) ≤ √(12932 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.718951806635 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12932 12932 (11 / 1000) ≤
    (0.008405696219 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12932) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.718951806635 : ℝ) ≤ √(12932 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12932)
  have hdiv : K / √(12932 : ℝ) ≤ K / 113.718951806635 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.718951806635 ≤ (0.008405696219 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12932.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12932 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12932 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12932 := gPlus_lower 12932
end BstLean.Part269.N12932

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12932
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035483746305 : ℝ) ≤ wn 12932 := by
  have hn : √(12932 : ℝ) ≤ 113.718951806636 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12932 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.718951806636 ≤ 2 / √(12932 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247284401 : ℝ) ≤ rhoBar 12932 BstLean.Part154.csC ∧
    rhoBar 12932 BstLean.Part154.csC ≤ 0.000247284784 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035483746305 : ℝ) / (1.295212 * 12932) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035483746306 : ℝ) / (1.29521 * 12932) := by gcongr
      _ ≤ (0.000247284784 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12932 BstLean.Part154.csC) ≤ 0.000989200286 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12932 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12932 BstLean.Part154.csC) (piBar (rhoBar 12932 BstLean.Part154.csC)) ≤ 0.000188877626 ∧
    cc1 (rhoBar 12932 BstLean.Part154.csC) (piBar (rhoBar 12932 BstLean.Part154.csC)) ≤ 0.000120184121 ∧
    cc2 (rhoBar 12932 BstLean.Part154.csC) ≤ 0.000069767843 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12932 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12932 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12932 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12932 BstLean.Part154.csC * nuR (rhoBar 12932 BstLean.Part154.csC)) ≤ 0.000494584856 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247284784 : ℝ) * 0.000989200286 := by gcongr
      _ ≤ (0.000494584856 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12932 BstLean.Part154.csC) * nuR (rhoBar 12932 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000989200286 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12932 BstLean.Part154.csC) * rhoBar 12932 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247284784 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247284784 / 2 + 0.399 * 0.000989200286 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188877626 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494584856 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120184121 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247284784 / 1.414213562 := by gcongr
      _ ≤ (0.000069767843 : ℝ) := by norm_num

end BstLean.Part269.N12932

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12932
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12932 BstLean.Part154.csC) (piBar (rhoBar 12932 BstLean.Part154.csC)) ≤ 1.54062E-7 := by
  have hr0 : 0 ≤ rhoBar 12932 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12932 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12932 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12932 BstLean.Part154.csC) (piBar (rhoBar 12932 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12932 BstLean.Part154.csC) (piBar (rhoBar 12932 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12932 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188877626 : ℝ) ^ 2 + 0.000120184121 ^ 2 + 3 * 0.000069767843 ^ 2 +
        2 * 0.797885 * 0.000188877626 * 0.000120184121 + 2 * 0.000188877626 * 0.000069767843 +
        4 * 0.797885 * 0.000120184121 * 0.000069767843 := by gcongr
    _ ≤ (1.54062E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12932 BstLean.Part154.csC Θ ≤ 0.002580489450 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12932 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12932 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12932 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12932 BstLean.Part154.csC) (piBar (rhoBar 12932 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12932 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035483746306 * 1.54062E-7 / (0.000247284401 : ℝ) := by gcongr
    _ ≤ 0.002580489450 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12932 BstLean.Part154.csC Θ ≤ 0.002862297805 + 0.000652049979 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12932 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12932 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12932 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035483746306 : ℝ) * ((2 * Θ * 0.000247284784 +
        (6863 / 10000) * 0.000247284784 * 12932 * 0.000989200286) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002862297805 + 0.000652049979 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12932 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12932 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12932 0.011 Θ ∧ gammaRatio 12932 0.011 Θ ≤ 0.000085010114 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12932 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035483746306 : ℝ) * 0.525 / ((1 - 0.011) * 12932) := by gcongr
      _ ≤ (0.000085010114 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12932 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12932 0.011 Θ) :=
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
    badAllowance 12932 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12932 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12932 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12932 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12932 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12932 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12932 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12932 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12932 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12932 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12932 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035483746306 : ℝ) * 12932 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12932 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003282856361 + 0.003232539429 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12932

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12932
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12932 BstLean.Part154.csC) (piBar (rhoBar 12932 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12932 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12932 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12932 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12932 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12932 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12932 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12932 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12932 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12932 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12932 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12932 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12932 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12932 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12932 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052006316227 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12932) ≤ 0.010501658362 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12932 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035483746306)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010501658362 + 2 * 0.737676 / 12932) := by gcongr
    _ ≤ (0.052006316227 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12932 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12932

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12932
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513871798 : ℝ) ≤ plow 12932 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12932) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052486539562)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354756962) : eMP 12932 0.011 xi bn ≤ 0.001166623719 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12932 : ℝ) * (1 - 0.011))) ≤ 0.000576865628 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001354756962 / (12932 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576865628 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576865628 : ℝ) + 3.141593 * 0.052486539562 / (12932 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001166623719 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052486539562)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354756962) : PiBarMP 12932 12 0.011 xi bn ≤ 0.159783336932 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12932 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036807023271 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.091768047015 : ℝ) ≤ √((12932 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.718951806635 : ℝ) ≤ √(12932 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12932) ≤ 0.122516150927 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036807023271 + 0.052486539562 * 1.772454 / (2 * (113.091768047015 : ℝ))) * (1 + 0.001166623719) +
        8 / (12932 * 113.718951806635) + 0.122516150927 := by gcongr
    _ ≤ (0.159783336932 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052486539562)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354756962) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281105726008) :
    parallelOracle 12932 0.011 xi bn cd ≤ 0.160755523931 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12932 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12932 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513871798 : ℝ) ≤ plow 12932 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.718951806635 : ℝ) ≤ √(12932 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281105726008 : ℝ) / (2 * 0.560513871798 * 113.718951806635)) * 0.159783336932 +
        0.281105726008 ^ 2 / (2 * 0.560513871798 * 113.718951806635) := by gcongr
    _ ≤ (0.160755523931 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052486539562) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354756962)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281105726008) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12932 12932 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513871798 : ℝ) ≤ plow 12932 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.718951806635 : ℝ) ≤ √(12932 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12932 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12932 Θ 1.22 ≤ 0.011661209315 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.718951806635 := by gcongr <;> linarith
      _ ≤ (0.011661209315 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12932 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12932 12932 0.011 ≤ 0.008405696219 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12932 12932 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12932 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12932 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12932 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12932 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160755523931 + 0.011661209315 + (0.008405696219 : ℝ) *
        (1 + 2 * (0.281105726008 + 0.011661209315) / (0.560513871798 * 113.718951806635))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12932]

end BstLean.Part269.N12932

/-! The original eight local profiles supply actual 12932 moment certificates. -/
namespace BstLean.Part269.N12932
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12932 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12932 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12932 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052486539562 ∧
    0 ≤ bN 12932 BstLean.Part154.csC (groupTheta g) ∧ bN 12932 BstLean.Part154.csC (groupTheta g) ≤ 0.001354756962 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12932 12932 0.011
      (momentAllowance 12932 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12932 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12932 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12932 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12932 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12932 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229099409781 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12932 0.011
      (momentAllowance 12932 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12932 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12932
/-! The actual computed-centre upper energy formula at 12932. -/
namespace BstLean.Part269.N12932
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12932

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12932
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12932)
open BstLean.Part268 (cell12932)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084840722854
  | 2 => 0.085772127973
  | 3 => 0.086700114793
  | 4 => 0.087625736089
  | 5 => 0.088550276225
  | 6 => 0.089475286924
  | 7 => 0.090402626667
  | 8 => 0.091334503813
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12932 12932 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12932 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12932

/-! Actual upper energy certificates on all 43 source endpoints at 12932. -/
namespace BstLean.Part269.N12932
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12932)
open BstLean.Part268 (cell12932)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12932 (gMinus 12932) (1 - (cell12932 i).lower) ≤ 1 ∧
    energyUpper 12932 (gMinus 12932) (BstLean.Part211.gPlus 12932)
      (finiteEnergy 12932 12932 0.011) (1 - (cell12932 i).lower) ≤
      (cell12932 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨10,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨11,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨12,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨13,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨14,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨15,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨16,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨17,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨18,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨19,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨20,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨21,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨22,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨23,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨24,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨25,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨26,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨27,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨28,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨29,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨30,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨31,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨32,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨33,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨34,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨35,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨36,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨37,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨38,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨39,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨40,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨41,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨42,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨43,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨44,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨45,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨46,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨47,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨48,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨49,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨50,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨51,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12932) (by norm_num)
        (q := 1 - (cell12932 ⟨52,by decide⟩).lower)
        (by norm_num [cell12932]) (by norm_num [cell12932])
      exact ⟨E.1,E.2.trans (by norm_num [cell12932])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12932

/-! Source-cell containment and simple scalar guards at 12932. -/
namespace BstLean.Part269.N12932
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12932)
open BstLean.Part268 (cell12932)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12932 ⟨10,by decide⟩).lower ∧ (cell12932 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12932 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12932 ⟨11,by decide⟩).lower ∧ (cell12932 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12932 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12932 ⟨12,by decide⟩).lower ∧ (cell12932 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12932 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12932 ⟨13,by decide⟩).lower ∧ (cell12932 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12932 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12932 ⟨14,by decide⟩).lower ∧ (cell12932 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12932 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12932 ⟨15,by decide⟩).lower ∧ (cell12932 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12932 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12932 ⟨16,by decide⟩).lower ∧ (cell12932 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12932 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12932 ⟨17,by decide⟩).lower ∧ (cell12932 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12932 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12932 ⟨18,by decide⟩).lower ∧ (cell12932 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12932 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12932 ⟨19,by decide⟩).lower ∧ (cell12932 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12932 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12932 ⟨20,by decide⟩).lower ∧ (cell12932 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12932 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12932 ⟨21,by decide⟩).lower ∧ (cell12932 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12932 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12932 ⟨22,by decide⟩).lower ∧ (cell12932 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12932 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12932 ⟨23,by decide⟩).lower ∧ (cell12932 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12932 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12932 ⟨24,by decide⟩).lower ∧ (cell12932 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12932 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12932 ⟨25,by decide⟩).lower ∧ (cell12932 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12932 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12932 ⟨26,by decide⟩).lower ∧ (cell12932 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12932 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12932 ⟨27,by decide⟩).lower ∧ (cell12932 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12932 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12932 ⟨28,by decide⟩).lower ∧ (cell12932 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12932 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12932 ⟨29,by decide⟩).lower ∧ (cell12932 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12932 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12932 ⟨30,by decide⟩).lower ∧ (cell12932 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12932 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12932 ⟨31,by decide⟩).lower ∧ (cell12932 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12932 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12932 ⟨32,by decide⟩).lower ∧ (cell12932 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12932 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12932 ⟨33,by decide⟩).lower ∧ (cell12932 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12932 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12932 ⟨34,by decide⟩).lower ∧ (cell12932 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12932 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12932 ⟨35,by decide⟩).lower ∧ (cell12932 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12932 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12932 ⟨36,by decide⟩).lower ∧ (cell12932 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12932 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12932 ⟨37,by decide⟩).lower ∧ (cell12932 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12932 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12932 ⟨38,by decide⟩).lower ∧ (cell12932 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12932 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12932 ⟨39,by decide⟩).lower ∧ (cell12932 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12932 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12932 ⟨40,by decide⟩).lower ∧ (cell12932 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12932 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12932 ⟨41,by decide⟩).lower ∧ (cell12932 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12932 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12932 ⟨42,by decide⟩).lower ∧ (cell12932 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12932 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12932 ⟨43,by decide⟩).lower ∧ (cell12932 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12932 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12932 ⟨44,by decide⟩).lower ∧ (cell12932 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12932 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12932 ⟨45,by decide⟩).lower ∧ (cell12932 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12932 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12932 ⟨46,by decide⟩).lower ∧ (cell12932 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12932 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12932 ⟨47,by decide⟩).lower ∧ (cell12932 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12932 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12932 ⟨48,by decide⟩).lower ∧ (cell12932 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12932 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12932 ⟨49,by decide⟩).lower ∧ (cell12932 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12932 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12932 ⟨50,by decide⟩).lower ∧ (cell12932 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12932 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12932 ⟨51,by decide⟩).lower ∧ (cell12932 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12932 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12932 ⟨52,by decide⟩).lower ∧ (cell12932 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12932 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12932 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12932 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12932,cell12932,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12932 i).lower ∧
    (cell12932 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12932 i).upper ≤ (0.532 : ℝ) ∧
    (cell12932 i).centre ≤ (0.1 : ℝ) ∧ (cell12932 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12932 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12932 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12932

/-! The local source numeric instances at 12932 have no network premises. -/
namespace BstLean.Part269.N12932
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12932)
open BstLean.Part268 (cell12932)

noncomputable def sourceNumerics12932 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12932 (cell12932 i)
      scalarRow12932.M scalarRow12932.H scalarRow12932.xi := by
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
    energy_allowance := scalarRow12932.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12932]
    centre_nonneg := (scalarRow12932.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12932])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12932
/-! Actual 12933 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12933
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12933 ≤ (1.035482362492 : ℝ) := by
  have hr : (113.723348526149 : ℝ) ≤ √(12933 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.723348526149 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12933 12933 (11 / 1000) ≤
    (0.008405371239 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12933) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.723348526149 : ℝ) ≤ √(12933 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12933)
  have hdiv : K / √(12933 : ℝ) ≤ K / 113.723348526149 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.723348526149 ≤ (0.008405371239 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12933.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12933 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12933 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12933 := gPlus_lower 12933
end BstLean.Part269.N12933

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12933
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035482362491 : ℝ) ≤ wn 12933 := by
  have hn : √(12933 : ℝ) ≤ 113.723348526150 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12933 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.723348526150 ≤ 2 / √(12933 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247264950 : ℝ) ≤ rhoBar 12933 BstLean.Part154.csC ∧
    rhoBar 12933 BstLean.Part154.csC ≤ 0.000247265333 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035482362491 : ℝ) / (1.295212 * 12933) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035482362492 : ℝ) / (1.29521 * 12933) := by gcongr
      _ ≤ (0.000247265333 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12933 BstLean.Part154.csC) ≤ 0.000989122473 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12933 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12933 BstLean.Part154.csC) (piBar (rhoBar 12933 BstLean.Part154.csC)) ≤ 0.000188862768 ∧
    cc1 (rhoBar 12933 BstLean.Part154.csC) (piBar (rhoBar 12933 BstLean.Part154.csC)) ≤ 0.000120174667 ∧
    cc2 (rhoBar 12933 BstLean.Part154.csC) ≤ 0.000069762355 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12933 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12933 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12933 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12933 BstLean.Part154.csC * nuR (rhoBar 12933 BstLean.Part154.csC)) ≤ 0.000494545952 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247265333 : ℝ) * 0.000989122473 := by gcongr
      _ ≤ (0.000494545952 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12933 BstLean.Part154.csC) * nuR (rhoBar 12933 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000989122473 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12933 BstLean.Part154.csC) * rhoBar 12933 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247265333 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247265333 / 2 + 0.399 * 0.000989122473 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188862768 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494545952 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120174667 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247265333 / 1.414213562 := by gcongr
      _ ≤ (0.000069762355 : ℝ) := by norm_num

end BstLean.Part269.N12933

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12933
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12933 BstLean.Part154.csC) (piBar (rhoBar 12933 BstLean.Part154.csC)) ≤ 1.54038E-7 := by
  have hr0 : 0 ≤ rhoBar 12933 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12933 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12933 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12933 BstLean.Part154.csC) (piBar (rhoBar 12933 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12933 BstLean.Part154.csC) (piBar (rhoBar 12933 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12933 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188862768 : ℝ) ^ 2 + 0.000120174667 ^ 2 + 3 * 0.000069762355 ^ 2 +
        2 * 0.797885 * 0.000188862768 * 0.000120174667 + 2 * 0.000188862768 * 0.000069762355 +
        4 * 0.797885 * 0.000120174667 * 0.000069762355 := by gcongr
    _ ≤ (1.54038E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12933 BstLean.Part154.csC Θ ≤ 0.002580286970 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12933 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12933 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12933 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12933 BstLean.Part154.csC) (piBar (rhoBar 12933 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12933 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035482362492 * 1.54038E-7 / (0.000247264950 : ℝ) := by gcongr
    _ ≤ 0.002580286970 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12933 BstLean.Part154.csC Θ ≤ 0.002862064998 + 0.000651997819 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12933 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12933 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12933 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035482362492 : ℝ) * ((2 * Θ * 0.000247265333 +
        (6863 / 10000) * 0.000247265333 * 12933 * 0.000989122473) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002862064998 + 0.000651997819 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12933 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12933 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12933 0.011 Θ ∧ gammaRatio 12933 0.011 Θ ≤ 0.000085003428 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12933 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035482362492 : ℝ) * 0.525 / ((1 - 0.011) * 12933) := by gcongr
      _ ≤ (0.000085003428 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12933 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12933 0.011 Θ) :=
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
    badAllowance 12933 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12933 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12933 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12933 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12933 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12933 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12933 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12933 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12933 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12933 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12933 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035482362492 : ℝ) * 12933 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12933 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003282623554 + 0.003232284789 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12933

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12933
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12933 BstLean.Part154.csC) (piBar (rhoBar 12933 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12933 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12933 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12933 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12933 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12933 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12933 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12933 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12933 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12933 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12933 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12933 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12933 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12933 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12933 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052004283972 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12933) ≤ 0.010501252351 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12933 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035482362492)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010501252351 + 2 * 0.737676 / 12933) := by gcongr
    _ ≤ (0.052004283972 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12933 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12933

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12933
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513915410 : ℝ) ≤ plow 12933 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12933) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052486173069)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354650660) : eMP 12933 0.011 xi bn ≤ 0.001166532764 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12933 : ℝ) * (1 - 0.011))) ≤ 0.000576820694 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001354650660 / (12933 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576820694 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576820694 : ℝ) + 3.141593 * 0.052486173069 / (12933 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001166532764 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052486173069)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354650660) : PiBarMP 12933 12 0.011 xi bn ≤ 0.159777131699 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12933 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036805579197 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.096140517702 : ℝ) ≤ √((12933 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.723348526149 : ℝ) ≤ √(12933 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12933) ≤ 0.122511414264 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036805579197 + 0.052486173069 * 1.772454 / (2 * (113.096140517702 : ℝ))) * (1 + 0.001166532764) +
        8 / (12933 * 113.723348526149) + 0.122511414264 := by gcongr
    _ ≤ (0.159777131699 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052486173069)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354650660) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281102893896) :
    parallelOracle 12933 0.011 xi bn cd ≤ 0.160749251315 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12933 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12933 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513915410 : ℝ) ≤ plow 12933 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.723348526149 : ℝ) ≤ √(12933 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281102893896 : ℝ) / (2 * 0.560513915410 * 113.723348526149)) * 0.159777131699 +
        0.281102893896 ^ 2 / (2 * 0.560513915410 * 113.723348526149) := by gcongr
    _ ≤ (0.160749251315 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052486173069) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354650660)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281102893896) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12933 12933 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513915410 : ℝ) ≤ plow 12933 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.723348526149 : ℝ) ≤ √(12933 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12933 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12933 Θ 1.22 ≤ 0.011660758474 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.723348526149 := by gcongr <;> linarith
      _ ≤ (0.011660758474 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12933 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12933 12933 0.011 ≤ 0.008405371239 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12933 12933 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12933 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12933 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12933 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12933 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160749251315 + 0.011660758474 + (0.008405371239 : ℝ) *
        (1 + 2 * (0.281102893896 + 0.011660758474) / (0.560513915410 * 113.723348526149))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12933]

end BstLean.Part269.N12933

/-! The original eight local profiles supply actual 12933 moment certificates. -/
namespace BstLean.Part269.N12933
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12933 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12933 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12933 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052486173069 ∧
    0 ≤ bN 12933 BstLean.Part154.csC (groupTheta g) ∧ bN 12933 BstLean.Part154.csC (groupTheta g) ≤ 0.001354650660 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12933 12933 0.011
      (momentAllowance 12933 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12933 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12933 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12933 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12933 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12933 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229098609924 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12933 0.011
      (momentAllowance 12933 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12933 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12933
/-! The actual computed-centre upper energy formula at 12933. -/
namespace BstLean.Part269.N12933
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12933

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12933
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12933)
open BstLean.Part268 (cell12933)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084838031651
  | 2 => 0.085769392128
  | 3 => 0.086697328590
  | 4 => 0.087622892448
  | 5 => 0.088547366448
  | 6 => 0.089472300412
  | 7 => 0.090399550607
  | 8 => 0.091331322819
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12933 12933 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12933 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12933

/-! Actual upper energy certificates on all 43 source endpoints at 12933. -/
namespace BstLean.Part269.N12933
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12933)
open BstLean.Part268 (cell12933)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12933 (gMinus 12933) (1 - (cell12933 i).lower) ≤ 1 ∧
    energyUpper 12933 (gMinus 12933) (BstLean.Part211.gPlus 12933)
      (finiteEnergy 12933 12933 0.011) (1 - (cell12933 i).lower) ≤
      (cell12933 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨10,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨11,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨12,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨13,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨14,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨15,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨16,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨17,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨18,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨19,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨20,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨21,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨22,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨23,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨24,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨25,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨26,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨27,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨28,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨29,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨30,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨31,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨32,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨33,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨34,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨35,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨36,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨37,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨38,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨39,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨40,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨41,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨42,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨43,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨44,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨45,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨46,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨47,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨48,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨49,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨50,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨51,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12933) (by norm_num)
        (q := 1 - (cell12933 ⟨52,by decide⟩).lower)
        (by norm_num [cell12933]) (by norm_num [cell12933])
      exact ⟨E.1,E.2.trans (by norm_num [cell12933])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12933

/-! Source-cell containment and simple scalar guards at 12933. -/
namespace BstLean.Part269.N12933
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12933)
open BstLean.Part268 (cell12933)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12933 ⟨10,by decide⟩).lower ∧ (cell12933 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12933 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12933 ⟨11,by decide⟩).lower ∧ (cell12933 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12933 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12933 ⟨12,by decide⟩).lower ∧ (cell12933 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12933 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12933 ⟨13,by decide⟩).lower ∧ (cell12933 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12933 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12933 ⟨14,by decide⟩).lower ∧ (cell12933 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12933 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12933 ⟨15,by decide⟩).lower ∧ (cell12933 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12933 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12933 ⟨16,by decide⟩).lower ∧ (cell12933 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12933 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12933 ⟨17,by decide⟩).lower ∧ (cell12933 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12933 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12933 ⟨18,by decide⟩).lower ∧ (cell12933 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12933 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12933 ⟨19,by decide⟩).lower ∧ (cell12933 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12933 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12933 ⟨20,by decide⟩).lower ∧ (cell12933 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12933 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12933 ⟨21,by decide⟩).lower ∧ (cell12933 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12933 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12933 ⟨22,by decide⟩).lower ∧ (cell12933 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12933 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12933 ⟨23,by decide⟩).lower ∧ (cell12933 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12933 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12933 ⟨24,by decide⟩).lower ∧ (cell12933 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12933 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12933 ⟨25,by decide⟩).lower ∧ (cell12933 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12933 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12933 ⟨26,by decide⟩).lower ∧ (cell12933 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12933 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12933 ⟨27,by decide⟩).lower ∧ (cell12933 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12933 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12933 ⟨28,by decide⟩).lower ∧ (cell12933 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12933 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12933 ⟨29,by decide⟩).lower ∧ (cell12933 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12933 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12933 ⟨30,by decide⟩).lower ∧ (cell12933 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12933 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12933 ⟨31,by decide⟩).lower ∧ (cell12933 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12933 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12933 ⟨32,by decide⟩).lower ∧ (cell12933 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12933 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12933 ⟨33,by decide⟩).lower ∧ (cell12933 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12933 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12933 ⟨34,by decide⟩).lower ∧ (cell12933 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12933 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12933 ⟨35,by decide⟩).lower ∧ (cell12933 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12933 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12933 ⟨36,by decide⟩).lower ∧ (cell12933 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12933 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12933 ⟨37,by decide⟩).lower ∧ (cell12933 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12933 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12933 ⟨38,by decide⟩).lower ∧ (cell12933 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12933 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12933 ⟨39,by decide⟩).lower ∧ (cell12933 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12933 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12933 ⟨40,by decide⟩).lower ∧ (cell12933 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12933 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12933 ⟨41,by decide⟩).lower ∧ (cell12933 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12933 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12933 ⟨42,by decide⟩).lower ∧ (cell12933 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12933 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12933 ⟨43,by decide⟩).lower ∧ (cell12933 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12933 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12933 ⟨44,by decide⟩).lower ∧ (cell12933 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12933 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12933 ⟨45,by decide⟩).lower ∧ (cell12933 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12933 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12933 ⟨46,by decide⟩).lower ∧ (cell12933 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12933 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12933 ⟨47,by decide⟩).lower ∧ (cell12933 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12933 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12933 ⟨48,by decide⟩).lower ∧ (cell12933 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12933 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12933 ⟨49,by decide⟩).lower ∧ (cell12933 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12933 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12933 ⟨50,by decide⟩).lower ∧ (cell12933 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12933 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12933 ⟨51,by decide⟩).lower ∧ (cell12933 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12933 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12933 ⟨52,by decide⟩).lower ∧ (cell12933 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12933 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12933 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12933 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12933,cell12933,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12933 i).lower ∧
    (cell12933 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12933 i).upper ≤ (0.532 : ℝ) ∧
    (cell12933 i).centre ≤ (0.1 : ℝ) ∧ (cell12933 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12933 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12933 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12933

/-! The local source numeric instances at 12933 have no network premises. -/
namespace BstLean.Part269.N12933
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12933)
open BstLean.Part268 (cell12933)

noncomputable def sourceNumerics12933 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12933 (cell12933 i)
      scalarRow12933.M scalarRow12933.H scalarRow12933.xi := by
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
    energy_allowance := scalarRow12933.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12933]
    centre_nonneg := (scalarRow12933.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12933])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12933
/-! Actual 12934 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12934
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12934 ≤ (1.035480978839 : ℝ) := by
  have hr : (113.727745075685 : ℝ) ≤ √(12934 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.727745075685 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12934 12934 (11 / 1000) ≤
    (0.008405046297 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12934) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.727745075685 : ℝ) ≤ √(12934 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12934)
  have hdiv : K / √(12934 : ℝ) ≤ K / 113.727745075685 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.727745075685 ≤ (0.008405046297 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12934.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12934 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12934 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12934 := gPlus_lower 12934
end BstLean.Part269.N12934

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12934
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035480978838 : ℝ) ≤ wn 12934 := by
  have hn : √(12934 : ℝ) ≤ 113.727745075686 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12934 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.727745075686 ≤ 2 / √(12934 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247245502 : ℝ) ≤ rhoBar 12934 BstLean.Part154.csC ∧
    rhoBar 12934 BstLean.Part154.csC ≤ 0.000247245885 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035480978838 : ℝ) / (1.295212 * 12934) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035480978839 : ℝ) / (1.29521 * 12934) := by gcongr
      _ ≤ (0.000247245885 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12934 BstLean.Part154.csC) ≤ 0.000989044671 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12934 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12934 BstLean.Part154.csC) (piBar (rhoBar 12934 BstLean.Part154.csC)) ≤ 0.000188847913 ∧
    cc1 (rhoBar 12934 BstLean.Part154.csC) (piBar (rhoBar 12934 BstLean.Part154.csC)) ≤ 0.000120165214 ∧
    cc2 (rhoBar 12934 BstLean.Part154.csC) ≤ 0.000069756868 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12934 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12934 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12934 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12934 BstLean.Part154.csC * nuR (rhoBar 12934 BstLean.Part154.csC)) ≤ 0.000494507053 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247245885 : ℝ) * 0.000989044671 := by gcongr
      _ ≤ (0.000494507053 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12934 BstLean.Part154.csC) * nuR (rhoBar 12934 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000989044671 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12934 BstLean.Part154.csC) * rhoBar 12934 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247245885 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247245885 / 2 + 0.399 * 0.000989044671 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188847913 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494507053 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120165214 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247245885 / 1.414213562 := by gcongr
      _ ≤ (0.000069756868 : ℝ) := by norm_num

end BstLean.Part269.N12934

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12934
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12934 BstLean.Part154.csC) (piBar (rhoBar 12934 BstLean.Part154.csC)) ≤ 1.54014E-7 := by
  have hr0 : 0 ≤ rhoBar 12934 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12934 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12934 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12934 BstLean.Part154.csC) (piBar (rhoBar 12934 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12934 BstLean.Part154.csC) (piBar (rhoBar 12934 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12934 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188847913 : ℝ) ^ 2 + 0.000120165214 ^ 2 + 3 * 0.000069756868 ^ 2 +
        2 * 0.797885 * 0.000188847913 * 0.000120165214 + 2 * 0.000188847913 * 0.000069756868 +
        4 * 0.797885 * 0.000120165214 * 0.000069756868 := by gcongr
    _ ≤ (1.54014E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12934 BstLean.Part154.csC Θ ≤ 0.002580084430 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12934 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12934 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12934 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12934 BstLean.Part154.csC) (piBar (rhoBar 12934 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12934 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035480978839 * 1.54014E-7 / (0.000247245502 : ℝ) := by gcongr
    _ ≤ 0.002580084430 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12934 BstLean.Part154.csC Θ ≤ 0.002861832225 + 0.000651945666 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12934 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12934 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12934 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035480978839 : ℝ) * ((2 * Θ * 0.000247245885 +
        (6863 / 10000) * 0.000247245885 * 12934 * 0.000989044671) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002861832225 + 0.000651945666 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12934 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12934 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12934 0.011 Θ ∧ gammaRatio 12934 0.011 Θ ≤ 0.000084996742 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12934 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035480978839 : ℝ) * 0.525 / ((1 - 0.011) * 12934) := by gcongr
      _ ≤ (0.000084996742 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12934 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12934 0.011 Θ) :=
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
    badAllowance 12934 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12934 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12934 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12934 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12934 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12934 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12934 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12934 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12934 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12934 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12934 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035480978839 : ℝ) * 12934 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12934 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003282390781 + 0.003232030096 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12934

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12934
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12934 BstLean.Part154.csC) (piBar (rhoBar 12934 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12934 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12934 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12934 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12934 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12934 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12934 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12934 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12934 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12934 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12934 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12934 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12934 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12934 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12934 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052002251959 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12934) ≤ 0.010500846388 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12934 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035480978839)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010500846388 + 2 * 0.737676 / 12934) := by gcongr
    _ ≤ (0.052002251959 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12934 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12934

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12934
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560513959014 : ℝ) ≤ plow 12934 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12934) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052485806582)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354544326) : eMP 12934 0.011 xi bn ≤ 0.001166441801 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12934 : ℝ) * (1 - 0.011))) ≤ 0.000576775756 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001354544326 / (12934 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576775756 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576775756 : ℝ) + 3.141593 * 0.052485806582 / (12934 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001166441801 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052485806582)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354544326) : PiBarMP 12934 12 0.011 xi bn ≤ 0.159770926526 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12934 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036804134632 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.100512819350 : ℝ) ≤ √((12934 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.727745075685 : ℝ) ≤ √(12934 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12934) ≤ 0.122506678151 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036804134632 + 0.052485806582 * 1.772454 / (2 * (113.100512819350 : ℝ))) * (1 + 0.001166441801) +
        8 / (12934 * 113.727745075685) + 0.122506678151 := by gcongr
    _ ≤ (0.159770926526 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052485806582)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354544326) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281100062036) :
    parallelOracle 12934 0.011 xi bn cd ≤ 0.160742978768 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12934 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12934 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560513959014 : ℝ) ≤ plow 12934 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.727745075685 : ℝ) ≤ √(12934 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281100062036 : ℝ) / (2 * 0.560513959014 * 113.727745075685)) * 0.159770926526 +
        0.281100062036 ^ 2 / (2 * 0.560513959014 * 113.727745075685) := by gcongr
    _ ≤ (0.160742978768 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052485806582) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354544326)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281100062036) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12934 12934 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560513959014 : ℝ) ≤ plow 12934 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.727745075685 : ℝ) ≤ √(12934 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12934 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12934 Θ 1.22 ≤ 0.011660307686 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.727745075685 := by gcongr <;> linarith
      _ ≤ (0.011660307686 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12934 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12934 12934 0.011 ≤ 0.008405046297 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12934 12934 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12934 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12934 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12934 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12934 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160742978768 + 0.011660307686 + (0.008405046297 : ℝ) *
        (1 + 2 * (0.281100062036 + 0.011660307686) / (0.560513959014 * 113.727745075685))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12934]

end BstLean.Part269.N12934

/-! The original eight local profiles supply actual 12934 moment certificates. -/
namespace BstLean.Part269.N12934
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12934 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12934 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12934 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052485806582 ∧
    0 ≤ bN 12934 BstLean.Part154.csC (groupTheta g) ∧ bN 12934 BstLean.Part154.csC (groupTheta g) ≤ 0.001354544326 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12934 12934 0.011
      (momentAllowance 12934 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12934 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12934 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12934 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12934 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12934 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229097810077 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12934 0.011
      (momentAllowance 12934 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12934 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12934
/-! The actual computed-centre upper energy formula at 12934. -/
namespace BstLean.Part269.N12934
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12934

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12934
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12934)
open BstLean.Part268 (cell12934)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084835341311
  | 2 => 0.085766657178
  | 3 => 0.086694543324
  | 4 => 0.087620049793
  | 5 => 0.088544457718
  | 6 => 0.089469315023
  | 7 => 0.090396475760
  | 8 => 0.091328143148
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12934 12934 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12934 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12934

/-! Actual upper energy certificates on all 43 source endpoints at 12934. -/
namespace BstLean.Part269.N12934
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12934)
open BstLean.Part268 (cell12934)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12934 (gMinus 12934) (1 - (cell12934 i).lower) ≤ 1 ∧
    energyUpper 12934 (gMinus 12934) (BstLean.Part211.gPlus 12934)
      (finiteEnergy 12934 12934 0.011) (1 - (cell12934 i).lower) ≤
      (cell12934 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨10,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨11,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨12,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨13,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨14,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨15,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨16,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨17,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨18,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨19,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨20,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨21,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨22,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨23,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨24,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨25,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨26,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨27,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨28,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨29,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨30,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨31,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨32,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨33,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨34,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨35,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨36,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨37,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨38,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨39,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨40,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨41,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨42,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨43,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨44,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨45,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨46,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨47,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨48,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨49,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨50,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨51,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12934) (by norm_num)
        (q := 1 - (cell12934 ⟨52,by decide⟩).lower)
        (by norm_num [cell12934]) (by norm_num [cell12934])
      exact ⟨E.1,E.2.trans (by norm_num [cell12934])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12934

/-! Source-cell containment and simple scalar guards at 12934. -/
namespace BstLean.Part269.N12934
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12934)
open BstLean.Part268 (cell12934)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12934 ⟨10,by decide⟩).lower ∧ (cell12934 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12934 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12934 ⟨11,by decide⟩).lower ∧ (cell12934 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12934 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12934 ⟨12,by decide⟩).lower ∧ (cell12934 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12934 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12934 ⟨13,by decide⟩).lower ∧ (cell12934 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12934 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12934 ⟨14,by decide⟩).lower ∧ (cell12934 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12934 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12934 ⟨15,by decide⟩).lower ∧ (cell12934 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12934 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12934 ⟨16,by decide⟩).lower ∧ (cell12934 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12934 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12934 ⟨17,by decide⟩).lower ∧ (cell12934 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12934 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12934 ⟨18,by decide⟩).lower ∧ (cell12934 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12934 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12934 ⟨19,by decide⟩).lower ∧ (cell12934 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12934 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12934 ⟨20,by decide⟩).lower ∧ (cell12934 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12934 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12934 ⟨21,by decide⟩).lower ∧ (cell12934 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12934 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12934 ⟨22,by decide⟩).lower ∧ (cell12934 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12934 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12934 ⟨23,by decide⟩).lower ∧ (cell12934 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12934 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12934 ⟨24,by decide⟩).lower ∧ (cell12934 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12934 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12934 ⟨25,by decide⟩).lower ∧ (cell12934 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12934 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12934 ⟨26,by decide⟩).lower ∧ (cell12934 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12934 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12934 ⟨27,by decide⟩).lower ∧ (cell12934 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12934 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12934 ⟨28,by decide⟩).lower ∧ (cell12934 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12934 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12934 ⟨29,by decide⟩).lower ∧ (cell12934 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12934 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12934 ⟨30,by decide⟩).lower ∧ (cell12934 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12934 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12934 ⟨31,by decide⟩).lower ∧ (cell12934 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12934 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12934 ⟨32,by decide⟩).lower ∧ (cell12934 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12934 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12934 ⟨33,by decide⟩).lower ∧ (cell12934 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12934 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12934 ⟨34,by decide⟩).lower ∧ (cell12934 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12934 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12934 ⟨35,by decide⟩).lower ∧ (cell12934 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12934 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12934 ⟨36,by decide⟩).lower ∧ (cell12934 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12934 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12934 ⟨37,by decide⟩).lower ∧ (cell12934 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12934 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12934 ⟨38,by decide⟩).lower ∧ (cell12934 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12934 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12934 ⟨39,by decide⟩).lower ∧ (cell12934 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12934 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12934 ⟨40,by decide⟩).lower ∧ (cell12934 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12934 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12934 ⟨41,by decide⟩).lower ∧ (cell12934 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12934 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12934 ⟨42,by decide⟩).lower ∧ (cell12934 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12934 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12934 ⟨43,by decide⟩).lower ∧ (cell12934 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12934 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12934 ⟨44,by decide⟩).lower ∧ (cell12934 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12934 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12934 ⟨45,by decide⟩).lower ∧ (cell12934 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12934 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12934 ⟨46,by decide⟩).lower ∧ (cell12934 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12934 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12934 ⟨47,by decide⟩).lower ∧ (cell12934 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12934 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12934 ⟨48,by decide⟩).lower ∧ (cell12934 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12934 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12934 ⟨49,by decide⟩).lower ∧ (cell12934 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12934 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12934 ⟨50,by decide⟩).lower ∧ (cell12934 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12934 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12934 ⟨51,by decide⟩).lower ∧ (cell12934 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12934 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12934 ⟨52,by decide⟩).lower ∧ (cell12934 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12934 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12934 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12934 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12934,cell12934,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12934 i).lower ∧
    (cell12934 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12934 i).upper ≤ (0.532 : ℝ) ∧
    (cell12934 i).centre ≤ (0.1 : ℝ) ∧ (cell12934 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12934 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12934 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12934

/-! The local source numeric instances at 12934 have no network premises. -/
namespace BstLean.Part269.N12934
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12934)
open BstLean.Part268 (cell12934)

noncomputable def sourceNumerics12934 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12934 (cell12934 i)
      scalarRow12934.M scalarRow12934.H scalarRow12934.xi := by
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
    energy_allowance := scalarRow12934.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12934]
    centre_nonneg := (scalarRow12934.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12934])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12934
/-! Actual 12935 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12935
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12935 ≤ (1.035479595348 : ℝ) := by
  have hr : (113.732141455263 : ℝ) ≤ √(12935 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.732141455263 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12935 12935 (11 / 1000) ≤
    (0.008404721393 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12935) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.732141455263 : ℝ) ≤ √(12935 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12935)
  have hdiv : K / √(12935 : ℝ) ≤ K / 113.732141455263 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.732141455263 ≤ (0.008404721393 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12935.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12935 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12935 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12935 := gPlus_lower 12935
end BstLean.Part269.N12935

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12935
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035479595347 : ℝ) ≤ wn 12935 := by
  have hn : √(12935 : ℝ) ≤ 113.732141455264 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12935 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.732141455264 ≤ 2 / √(12935 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247226058 : ℝ) ≤ rhoBar 12935 BstLean.Part154.csC ∧
    rhoBar 12935 BstLean.Part154.csC ≤ 0.000247226440 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035479595347 : ℝ) / (1.295212 * 12935) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035479595348 : ℝ) / (1.29521 * 12935) := by gcongr
      _ ≤ (0.000247226440 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12935 BstLean.Part154.csC) ≤ 0.000988966881 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12935 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12935 BstLean.Part154.csC) (piBar (rhoBar 12935 BstLean.Part154.csC)) ≤ 0.000188833060 ∧
    cc1 (rhoBar 12935 BstLean.Part154.csC) (piBar (rhoBar 12935 BstLean.Part154.csC)) ≤ 0.000120155764 ∧
    cc2 (rhoBar 12935 BstLean.Part154.csC) ≤ 0.000069751382 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12935 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12935 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12935 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12935 BstLean.Part154.csC * nuR (rhoBar 12935 BstLean.Part154.csC)) ≤ 0.000494468161 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247226440 : ℝ) * 0.000988966881 := by gcongr
      _ ≤ (0.000494468161 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12935 BstLean.Part154.csC) * nuR (rhoBar 12935 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000988966881 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12935 BstLean.Part154.csC) * rhoBar 12935 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247226440 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247226440 / 2 + 0.399 * 0.000988966881 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188833060 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494468161 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120155764 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247226440 / 1.414213562 := by gcongr
      _ ≤ (0.000069751382 : ℝ) := by norm_num

end BstLean.Part269.N12935

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12935
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12935 BstLean.Part154.csC) (piBar (rhoBar 12935 BstLean.Part154.csC)) ≤ 1.53990E-7 := by
  have hr0 : 0 ≤ rhoBar 12935 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12935 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12935 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12935 BstLean.Part154.csC) (piBar (rhoBar 12935 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12935 BstLean.Part154.csC) (piBar (rhoBar 12935 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12935 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188833060 : ℝ) ^ 2 + 0.000120155764 ^ 2 + 3 * 0.000069751382 ^ 2 +
        2 * 0.797885 * 0.000188833060 * 0.000120155764 + 2 * 0.000188833060 * 0.000069751382 +
        4 * 0.797885 * 0.000120155764 * 0.000069751382 := by gcongr
    _ ≤ (1.53990E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12935 BstLean.Part154.csC Θ ≤ 0.002579881817 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12935 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12935 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12935 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12935 BstLean.Part154.csC) (piBar (rhoBar 12935 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12935 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035479595348 * 1.53990E-7 / (0.000247226058 : ℝ) := by gcongr
    _ ≤ 0.002579881817 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12935 BstLean.Part154.csC Θ ≤ 0.002861599488 + 0.000651893522 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12935 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12935 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12935 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035479595348 : ℝ) * ((2 * Θ * 0.000247226440 +
        (6863 / 10000) * 0.000247226440 * 12935 * 0.000988966881) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002861599488 + 0.000651893522 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12935 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12935 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12935 0.011 Θ ∧ gammaRatio 12935 0.011 Θ ≤ 0.000084990057 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12935 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035479595348 : ℝ) * 0.525 / ((1 - 0.011) * 12935) := by gcongr
      _ ≤ (0.000084990057 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12935 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12935 0.011 Θ) :=
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
    badAllowance 12935 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12935 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12935 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12935 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12935 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12935 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12935 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12935 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12935 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12935 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12935 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035479595348 : ℝ) * 12935 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12935 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003282158044 + 0.003231775339 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12935

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12935
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12935 BstLean.Part154.csC) (piBar (rhoBar 12935 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12935 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12935 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12935 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12935 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12935 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12935 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12935 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12935 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12935 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12935 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12935 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12935 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12935 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12935 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052000220183 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12935) ≤ 0.010500440472 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12935 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035479595348)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010500440472 + 2 * 0.737676 / 12935) := by gcongr
    _ ≤ (0.052000220183 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12935 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12935

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12935
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514002613 : ℝ) ≤ plow 12935 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12935) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052485440097)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354437954) : eMP 12935 0.011 xi bn ≤ 0.001166350831 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12935 : ℝ) * (1 - 0.011))) ≤ 0.000576730814 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001354437954 / (12935 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576730814 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576730814 : ℝ) + 3.141593 * 0.052485440097 / (12935 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001166350831 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052485440097)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354437954) : PiBarMP 12935 12 0.011 xi bn ≤ 0.159764721332 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12935 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036802689495 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.104884951977 : ℝ) ≤ √((12935 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.732141455263 : ℝ) ≤ √(12935 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12935) ≤ 0.122501942587 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036802689495 + 0.052485440097 * 1.772454 / (2 * (113.104884951977 : ℝ))) * (1 + 0.001166350831) +
        8 / (12935 * 113.732141455263) + 0.122501942587 := by gcongr
    _ ≤ (0.159764721332 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052485440097)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354437954) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281097230415) :
    parallelOracle 12935 0.011 xi bn cd ≤ 0.160736706207 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12935 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12935 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514002613 : ℝ) ≤ plow 12935 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.732141455263 : ℝ) ≤ √(12935 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281097230415 : ℝ) / (2 * 0.560514002613 * 113.732141455263)) * 0.159764721332 +
        0.281097230415 ^ 2 / (2 * 0.560514002613 * 113.732141455263) := by gcongr
    _ ≤ (0.160736706207 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052485440097) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354437954)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281097230415) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12935 12935 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514002613 : ℝ) ≤ plow 12935 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.732141455263 : ℝ) ≤ √(12935 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12935 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12935 Θ 1.22 ≤ 0.011659856951 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.732141455263 := by gcongr <;> linarith
      _ ≤ (0.011659856951 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12935 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12935 12935 0.011 ≤ 0.008404721393 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12935 12935 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12935 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12935 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12935 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12935 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160736706207 + 0.011659856951 + (0.008404721393 : ℝ) *
        (1 + 2 * (0.281097230415 + 0.011659856951) / (0.560514002613 * 113.732141455263))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12935]

end BstLean.Part269.N12935

/-! The original eight local profiles supply actual 12935 moment certificates. -/
namespace BstLean.Part269.N12935
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12935 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12935 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12935 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052485440097 ∧
    0 ≤ bN 12935 BstLean.Part154.csC (groupTheta g) ∧ bN 12935 BstLean.Part154.csC (groupTheta g) ≤ 0.001354437954 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12935 12935 0.011
      (momentAllowance 12935 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12935 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12935 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12935 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12935 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12935 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229097010232 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12935 0.011
      (momentAllowance 12935 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12935 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12935
/-! The actual computed-centre upper energy formula at 12935. -/
namespace BstLean.Part269.N12935
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12935

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12935
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12935)
open BstLean.Part268 (cell12935)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084832651834
  | 2 => 0.085763923124
  | 3 => 0.086691758994
  | 4 => 0.087617208125
  | 5 => 0.088541550035
  | 6 => 0.089466330755
  | 7 => 0.090393402126
  | 8 => 0.091324964798
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12935 12935 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12935 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12935

/-! Actual upper energy certificates on all 43 source endpoints at 12935. -/
namespace BstLean.Part269.N12935
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12935)
open BstLean.Part268 (cell12935)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12935 (gMinus 12935) (1 - (cell12935 i).lower) ≤ 1 ∧
    energyUpper 12935 (gMinus 12935) (BstLean.Part211.gPlus 12935)
      (finiteEnergy 12935 12935 0.011) (1 - (cell12935 i).lower) ≤
      (cell12935 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨10,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨11,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨12,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨13,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨14,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨15,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨16,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨17,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨18,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨19,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨20,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨21,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨22,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨23,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨24,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨25,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨26,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨27,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨28,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨29,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨30,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨31,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨32,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨33,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨34,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨35,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨36,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨37,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨38,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨39,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨40,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨41,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨42,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨43,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨44,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨45,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨46,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨47,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨48,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨49,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨50,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨51,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12935) (by norm_num)
        (q := 1 - (cell12935 ⟨52,by decide⟩).lower)
        (by norm_num [cell12935]) (by norm_num [cell12935])
      exact ⟨E.1,E.2.trans (by norm_num [cell12935])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12935

/-! Source-cell containment and simple scalar guards at 12935. -/
namespace BstLean.Part269.N12935
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12935)
open BstLean.Part268 (cell12935)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12935 ⟨10,by decide⟩).lower ∧ (cell12935 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12935 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12935 ⟨11,by decide⟩).lower ∧ (cell12935 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12935 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12935 ⟨12,by decide⟩).lower ∧ (cell12935 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12935 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12935 ⟨13,by decide⟩).lower ∧ (cell12935 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12935 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12935 ⟨14,by decide⟩).lower ∧ (cell12935 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12935 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12935 ⟨15,by decide⟩).lower ∧ (cell12935 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12935 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12935 ⟨16,by decide⟩).lower ∧ (cell12935 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12935 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12935 ⟨17,by decide⟩).lower ∧ (cell12935 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12935 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12935 ⟨18,by decide⟩).lower ∧ (cell12935 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12935 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12935 ⟨19,by decide⟩).lower ∧ (cell12935 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12935 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12935 ⟨20,by decide⟩).lower ∧ (cell12935 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12935 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12935 ⟨21,by decide⟩).lower ∧ (cell12935 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12935 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12935 ⟨22,by decide⟩).lower ∧ (cell12935 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12935 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12935 ⟨23,by decide⟩).lower ∧ (cell12935 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12935 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12935 ⟨24,by decide⟩).lower ∧ (cell12935 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12935 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12935 ⟨25,by decide⟩).lower ∧ (cell12935 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12935 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12935 ⟨26,by decide⟩).lower ∧ (cell12935 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12935 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12935 ⟨27,by decide⟩).lower ∧ (cell12935 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12935 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12935 ⟨28,by decide⟩).lower ∧ (cell12935 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12935 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12935 ⟨29,by decide⟩).lower ∧ (cell12935 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12935 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12935 ⟨30,by decide⟩).lower ∧ (cell12935 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12935 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12935 ⟨31,by decide⟩).lower ∧ (cell12935 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12935 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12935 ⟨32,by decide⟩).lower ∧ (cell12935 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12935 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12935 ⟨33,by decide⟩).lower ∧ (cell12935 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12935 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12935 ⟨34,by decide⟩).lower ∧ (cell12935 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12935 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12935 ⟨35,by decide⟩).lower ∧ (cell12935 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12935 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12935 ⟨36,by decide⟩).lower ∧ (cell12935 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12935 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12935 ⟨37,by decide⟩).lower ∧ (cell12935 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12935 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12935 ⟨38,by decide⟩).lower ∧ (cell12935 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12935 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12935 ⟨39,by decide⟩).lower ∧ (cell12935 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12935 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12935 ⟨40,by decide⟩).lower ∧ (cell12935 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12935 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12935 ⟨41,by decide⟩).lower ∧ (cell12935 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12935 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12935 ⟨42,by decide⟩).lower ∧ (cell12935 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12935 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12935 ⟨43,by decide⟩).lower ∧ (cell12935 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12935 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12935 ⟨44,by decide⟩).lower ∧ (cell12935 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12935 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12935 ⟨45,by decide⟩).lower ∧ (cell12935 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12935 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12935 ⟨46,by decide⟩).lower ∧ (cell12935 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12935 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12935 ⟨47,by decide⟩).lower ∧ (cell12935 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12935 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12935 ⟨48,by decide⟩).lower ∧ (cell12935 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12935 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12935 ⟨49,by decide⟩).lower ∧ (cell12935 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12935 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12935 ⟨50,by decide⟩).lower ∧ (cell12935 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12935 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12935 ⟨51,by decide⟩).lower ∧ (cell12935 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12935 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12935 ⟨52,by decide⟩).lower ∧ (cell12935 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12935 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12935 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12935 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12935,cell12935,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12935 i).lower ∧
    (cell12935 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12935 i).upper ≤ (0.532 : ℝ) ∧
    (cell12935 i).centre ≤ (0.1 : ℝ) ∧ (cell12935 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12935 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12935 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12935

/-! The local source numeric instances at 12935 have no network premises. -/
namespace BstLean.Part269.N12935
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12935)
open BstLean.Part268 (cell12935)

noncomputable def sourceNumerics12935 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12935 (cell12935 i)
      scalarRow12935.M scalarRow12935.H scalarRow12935.xi := by
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
    energy_allowance := scalarRow12935.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12935]
    centre_nonneg := (scalarRow12935.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12935])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12935
/-! Actual 12936 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12936
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12936 ≤ (1.035478212018 : ℝ) := by
  have hr : (113.736537664903 : ℝ) ≤ √(12936 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.736537664903 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12936 12936 (11 / 1000) ≤
    (0.008404396526 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12936) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.736537664903 : ℝ) ≤ √(12936 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12936)
  have hdiv : K / √(12936 : ℝ) ≤ K / 113.736537664903 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.736537664903 ≤ (0.008404396526 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12936.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12936 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12936 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12936 := gPlus_lower 12936
end BstLean.Part269.N12936

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12936
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035478212017 : ℝ) ≤ wn 12936 := by
  have hn : √(12936 : ℝ) ≤ 113.736537664904 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12936 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.736537664904 ≤ 2 / √(12936 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247206616 : ℝ) ≤ rhoBar 12936 BstLean.Part154.csC ∧
    rhoBar 12936 BstLean.Part154.csC ≤ 0.000247206999 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035478212017 : ℝ) / (1.295212 * 12936) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035478212018 : ℝ) / (1.29521 * 12936) := by gcongr
      _ ≤ (0.000247206999 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12936 BstLean.Part154.csC) ≤ 0.000988889108 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12936 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12936 BstLean.Part154.csC) (piBar (rhoBar 12936 BstLean.Part154.csC)) ≤ 0.000188818211 ∧
    cc1 (rhoBar 12936 BstLean.Part154.csC) (piBar (rhoBar 12936 BstLean.Part154.csC)) ≤ 0.000120146315 ∧
    cc2 (rhoBar 12936 BstLean.Part154.csC) ≤ 0.000069745897 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12936 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12936 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12936 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12936 BstLean.Part154.csC * nuR (rhoBar 12936 BstLean.Part154.csC)) ≤ 0.000494429276 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247206999 : ℝ) * 0.000988889108 := by gcongr
      _ ≤ (0.000494429276 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12936 BstLean.Part154.csC) * nuR (rhoBar 12936 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000988889108 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12936 BstLean.Part154.csC) * rhoBar 12936 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247206999 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247206999 / 2 + 0.399 * 0.000988889108 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188818211 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494429276 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120146315 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247206999 / 1.414213562 := by gcongr
      _ ≤ (0.000069745897 : ℝ) := by norm_num

end BstLean.Part269.N12936

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12936
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12936 BstLean.Part154.csC) (piBar (rhoBar 12936 BstLean.Part154.csC)) ≤ 1.53966E-7 := by
  have hr0 : 0 ≤ rhoBar 12936 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12936 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12936 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12936 BstLean.Part154.csC) (piBar (rhoBar 12936 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12936 BstLean.Part154.csC) (piBar (rhoBar 12936 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12936 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188818211 : ℝ) ^ 2 + 0.000120146315 ^ 2 + 3 * 0.000069745897 ^ 2 +
        2 * 0.797885 * 0.000188818211 * 0.000120146315 + 2 * 0.000188818211 * 0.000069745897 +
        4 * 0.797885 * 0.000120146315 * 0.000069745897 := by gcongr
    _ ≤ (1.53966E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12936 BstLean.Part154.csC Θ ≤ 0.002579679153 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12936 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12936 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12936 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12936 BstLean.Part154.csC) (piBar (rhoBar 12936 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12936 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035478212018 * 1.53966E-7 / (0.000247206616 : ℝ) := by gcongr
    _ ≤ 0.002579679153 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12936 BstLean.Part154.csC Θ ≤ 0.002861366814 + 0.000651841389 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12936 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12936 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12936 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035478212018 : ℝ) * ((2 * Θ * 0.000247206999 +
        (6863 / 10000) * 0.000247206999 * 12936 * 0.000988889108) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002861366814 + 0.000651841389 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12936 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12936 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12936 0.011 Θ ∧ gammaRatio 12936 0.011 Θ ≤ 0.000084983374 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12936 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035478212018 : ℝ) * 0.525 / ((1 - 0.011) * 12936) := by gcongr
      _ ≤ (0.000084983374 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12936 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12936 0.011 Θ) :=
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
    badAllowance 12936 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12936 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12936 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12936 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12936 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12936 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12936 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12936 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12936 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12936 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12936 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035478212018 : ℝ) * 12936 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12936 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003281925370 + 0.003231520542 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12936

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12936
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12936 BstLean.Part154.csC) (piBar (rhoBar 12936 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12936 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12936 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12936 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12936 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12936 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12936 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12936 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12936 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12936 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12936 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12936 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12936 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12936 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12936 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051998188643 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12936) ≤ 0.010500034603 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12936 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035478212018)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010500034603 + 2 * 0.737676 / 12936) := by gcongr
    _ ≤ (0.051998188643 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12936 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12936

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12936
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514046204 : ℝ) ≤ plow 12936 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12936) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052485073655)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354331556) : eMP 12936 0.011 xi bn ≤ 0.001166259856 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12936 : ℝ) * (1 - 0.011))) ≤ 0.000576685870 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001354331556 / (12936 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576685870 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576685870 : ℝ) + 3.141593 * 0.052485073655 / (12936 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001166259856 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052485073655)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354331556) : PiBarMP 12936 12 0.011 xi bn ≤ 0.159758516279 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12936 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036801243947 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.109256915603 : ℝ) ≤ √((12936 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.736537664903 : ℝ) ≤ √(12936 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12936) ≤ 0.122497207572 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036801243947 + 0.052485073655 * 1.772454 / (2 * (113.109256915603 : ℝ))) * (1 + 0.001166259856) +
        8 / (12936 * 113.736537664903) + 0.122497207572 := by gcongr
    _ ≤ (0.159758516279 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052485073655)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354331556) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281094399121) :
    parallelOracle 12936 0.011 xi bn cd ≤ 0.160730433798 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12936 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12936 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514046204 : ℝ) ≤ plow 12936 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.736537664903 : ℝ) ≤ √(12936 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281094399121 : ℝ) / (2 * 0.560514046204 * 113.736537664903)) * 0.159758516279 +
        0.281094399121 ^ 2 / (2 * 0.560514046204 * 113.736537664903) := by gcongr
    _ ≤ (0.160730433798 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052485073655) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354331556)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281094399121) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12936 12936 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514046204 : ℝ) ≤ plow 12936 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.736537664903 : ℝ) ≤ √(12936 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12936 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12936 Θ 1.22 ≤ 0.011659406267 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.736537664903 := by gcongr <;> linarith
      _ ≤ (0.011659406267 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12936 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12936 12936 0.011 ≤ 0.008404396526 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12936 12936 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12936 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12936 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12936 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12936 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160730433798 + 0.011659406267 + (0.008404396526 : ℝ) *
        (1 + 2 * (0.281094399121 + 0.011659406267) / (0.560514046204 * 113.736537664903))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12936]

end BstLean.Part269.N12936

/-! The original eight local profiles supply actual 12936 moment certificates. -/
namespace BstLean.Part269.N12936
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12936 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12936 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12936 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052485073655 ∧
    0 ≤ bN 12936 BstLean.Part154.csC (groupTheta g) ∧ bN 12936 BstLean.Part154.csC (groupTheta g) ≤ 0.001354331556 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12936 12936 0.011
      (momentAllowance 12936 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12936 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12936 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12936 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12936 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12936 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229096210478 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12936 0.011
      (momentAllowance 12936 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12936 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12936
/-! The actual computed-centre upper energy formula at 12936. -/
namespace BstLean.Part269.N12936
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12936

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12936
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12936)
open BstLean.Part268 (cell12936)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084829963217
  | 2 => 0.085761189963
  | 3 => 0.086688975598
  | 4 => 0.087614367440
  | 5 => 0.088538643398
  | 6 => 0.089463347608
  | 7 => 0.090390329702
  | 8 => 0.091321787768
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12936 12936 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12936 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12936

/-! Actual upper energy certificates on all 43 source endpoints at 12936. -/
namespace BstLean.Part269.N12936
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12936)
open BstLean.Part268 (cell12936)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12936 (gMinus 12936) (1 - (cell12936 i).lower) ≤ 1 ∧
    energyUpper 12936 (gMinus 12936) (BstLean.Part211.gPlus 12936)
      (finiteEnergy 12936 12936 0.011) (1 - (cell12936 i).lower) ≤
      (cell12936 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨10,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨11,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨12,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨13,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨14,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨15,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨16,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨17,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨18,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨19,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨20,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨21,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨22,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨23,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨24,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨25,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨26,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨27,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨28,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨29,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨30,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨31,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨32,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨33,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨34,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨35,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨36,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨37,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨38,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨39,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨40,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨41,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨42,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨43,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨44,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨45,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨46,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨47,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨48,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨49,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨50,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨51,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12936) (by norm_num)
        (q := 1 - (cell12936 ⟨52,by decide⟩).lower)
        (by norm_num [cell12936]) (by norm_num [cell12936])
      exact ⟨E.1,E.2.trans (by norm_num [cell12936])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12936

/-! Source-cell containment and simple scalar guards at 12936. -/
namespace BstLean.Part269.N12936
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12936)
open BstLean.Part268 (cell12936)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12936 ⟨10,by decide⟩).lower ∧ (cell12936 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12936 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12936 ⟨11,by decide⟩).lower ∧ (cell12936 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12936 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12936 ⟨12,by decide⟩).lower ∧ (cell12936 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12936 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12936 ⟨13,by decide⟩).lower ∧ (cell12936 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12936 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12936 ⟨14,by decide⟩).lower ∧ (cell12936 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12936 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12936 ⟨15,by decide⟩).lower ∧ (cell12936 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12936 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12936 ⟨16,by decide⟩).lower ∧ (cell12936 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12936 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12936 ⟨17,by decide⟩).lower ∧ (cell12936 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12936 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12936 ⟨18,by decide⟩).lower ∧ (cell12936 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12936 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12936 ⟨19,by decide⟩).lower ∧ (cell12936 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12936 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12936 ⟨20,by decide⟩).lower ∧ (cell12936 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12936 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12936 ⟨21,by decide⟩).lower ∧ (cell12936 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12936 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12936 ⟨22,by decide⟩).lower ∧ (cell12936 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12936 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12936 ⟨23,by decide⟩).lower ∧ (cell12936 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12936 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12936 ⟨24,by decide⟩).lower ∧ (cell12936 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12936 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12936 ⟨25,by decide⟩).lower ∧ (cell12936 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12936 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12936 ⟨26,by decide⟩).lower ∧ (cell12936 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12936 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12936 ⟨27,by decide⟩).lower ∧ (cell12936 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12936 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12936 ⟨28,by decide⟩).lower ∧ (cell12936 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12936 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12936 ⟨29,by decide⟩).lower ∧ (cell12936 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12936 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12936 ⟨30,by decide⟩).lower ∧ (cell12936 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12936 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12936 ⟨31,by decide⟩).lower ∧ (cell12936 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12936 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12936 ⟨32,by decide⟩).lower ∧ (cell12936 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12936 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12936 ⟨33,by decide⟩).lower ∧ (cell12936 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12936 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12936 ⟨34,by decide⟩).lower ∧ (cell12936 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12936 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12936 ⟨35,by decide⟩).lower ∧ (cell12936 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12936 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12936 ⟨36,by decide⟩).lower ∧ (cell12936 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12936 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12936 ⟨37,by decide⟩).lower ∧ (cell12936 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12936 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12936 ⟨38,by decide⟩).lower ∧ (cell12936 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12936 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12936 ⟨39,by decide⟩).lower ∧ (cell12936 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12936 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12936 ⟨40,by decide⟩).lower ∧ (cell12936 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12936 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12936 ⟨41,by decide⟩).lower ∧ (cell12936 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12936 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12936 ⟨42,by decide⟩).lower ∧ (cell12936 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12936 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12936 ⟨43,by decide⟩).lower ∧ (cell12936 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12936 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12936 ⟨44,by decide⟩).lower ∧ (cell12936 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12936 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12936 ⟨45,by decide⟩).lower ∧ (cell12936 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12936 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12936 ⟨46,by decide⟩).lower ∧ (cell12936 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12936 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12936 ⟨47,by decide⟩).lower ∧ (cell12936 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12936 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12936 ⟨48,by decide⟩).lower ∧ (cell12936 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12936 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12936 ⟨49,by decide⟩).lower ∧ (cell12936 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12936 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12936 ⟨50,by decide⟩).lower ∧ (cell12936 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12936 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12936 ⟨51,by decide⟩).lower ∧ (cell12936 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12936 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12936 ⟨52,by decide⟩).lower ∧ (cell12936 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12936 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12936 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12936 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12936,cell12936,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12936 i).lower ∧
    (cell12936 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12936 i).upper ≤ (0.532 : ℝ) ∧
    (cell12936 i).centre ≤ (0.1 : ℝ) ∧ (cell12936 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12936 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12936 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12936

/-! The local source numeric instances at 12936 have no network premises. -/
namespace BstLean.Part269.N12936
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12936)
open BstLean.Part268 (cell12936)

noncomputable def sourceNumerics12936 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12936 (cell12936 i)
      scalarRow12936.M scalarRow12936.H scalarRow12936.xi := by
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
    energy_allowance := scalarRow12936.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12936]
    centre_nonneg := (scalarRow12936.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12936])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12936
/-! Actual 12937 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12937
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12937 ≤ (1.035476828849 : ℝ) := by
  have hr : (113.740933704625 : ℝ) ≤ √(12937 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.740933704625 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12937 12937 (11 / 1000) ≤
    (0.008404071698 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12937) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.740933704625 : ℝ) ≤ √(12937 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12937)
  have hdiv : K / √(12937 : ℝ) ≤ K / 113.740933704625 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.740933704625 ≤ (0.008404071698 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12937.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12937 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12937 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12937 := gPlus_lower 12937
end BstLean.Part269.N12937

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12937
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035476828848 : ℝ) ≤ wn 12937 := by
  have hn : √(12937 : ℝ) ≤ 113.740933704626 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12937 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.740933704626 ≤ 2 / √(12937 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247187177 : ℝ) ≤ rhoBar 12937 BstLean.Part154.csC ∧
    rhoBar 12937 BstLean.Part154.csC ≤ 0.000247187560 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035476828848 : ℝ) / (1.295212 * 12937) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035476828849 : ℝ) / (1.29521 * 12937) := by gcongr
      _ ≤ (0.000247187560 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12937 BstLean.Part154.csC) ≤ 0.000988811342 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12937 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12937 BstLean.Part154.csC) (piBar (rhoBar 12937 BstLean.Part154.csC)) ≤ 0.000188803362 ∧
    cc1 (rhoBar 12937 BstLean.Part154.csC) (piBar (rhoBar 12937 BstLean.Part154.csC)) ≤ 0.000120136867 ∧
    cc2 (rhoBar 12937 BstLean.Part154.csC) ≤ 0.000069740412 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12937 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12937 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12937 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12937 BstLean.Part154.csC * nuR (rhoBar 12937 BstLean.Part154.csC)) ≤ 0.000494390396 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247187560 : ℝ) * 0.000988811342 := by gcongr
      _ ≤ (0.000494390396 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12937 BstLean.Part154.csC) * nuR (rhoBar 12937 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000988811342 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12937 BstLean.Part154.csC) * rhoBar 12937 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247187560 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247187560 / 2 + 0.399 * 0.000988811342 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000188803362 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000494390396 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120136867 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247187560 / 1.414213562 := by gcongr
      _ ≤ (0.000069740412 : ℝ) := by norm_num

end BstLean.Part269.N12937

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12937
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12937 BstLean.Part154.csC) (piBar (rhoBar 12937 BstLean.Part154.csC)) ≤ 1.53941E-7 := by
  have hr0 : 0 ≤ rhoBar 12937 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12937 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12937 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12937 BstLean.Part154.csC) (piBar (rhoBar 12937 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12937 BstLean.Part154.csC) (piBar (rhoBar 12937 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12937 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000188803362 : ℝ) ^ 2 + 0.000120136867 ^ 2 + 3 * 0.000069740412 ^ 2 +
        2 * 0.797885 * 0.000188803362 * 0.000120136867 + 2 * 0.000188803362 * 0.000069740412 +
        4 * 0.797885 * 0.000120136867 * 0.000069740412 := by gcongr
    _ ≤ (1.53941E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12937 BstLean.Part154.csC Θ ≤ 0.002579459671 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12937 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12937 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12937 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12937 BstLean.Part154.csC) (piBar (rhoBar 12937 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12937 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035476828849 * 1.53941E-7 / (0.000247187177 : ℝ) := by gcongr
    _ ≤ 0.002579459671 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12937 BstLean.Part154.csC Θ ≤ 0.002861134150 + 0.000651789261 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12937 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12937 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12937 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035476828849 : ℝ) * ((2 * Θ * 0.000247187560 +
        (6863 / 10000) * 0.000247187560 * 12937 * 0.000988811342) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002861134150 + 0.000651789261 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12937 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12937 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12937 0.011 Θ ∧ gammaRatio 12937 0.011 Θ ≤ 0.000084976691 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12937 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035476828849 : ℝ) * 0.525 / ((1 - 0.011) * 12937) := by gcongr
      _ ≤ (0.000084976691 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12937 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12937 0.011 Θ) :=
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
    badAllowance 12937 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000420558556 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12937 BstLean.Part154.csC) 1.22 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 2 (rhoBar 12937 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12937 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12937 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12937 0.011 Θ) 1.12 ≤ 1.8602E-8 := by
    have he : (17.8 : ℝ) ≤ gap 1 (gammaRatio 12937 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12937 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12937 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12937 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12937 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035476828849 : ℝ) * 12937 *
        (1.5230E-8 / 1.1045361 + 1.8602E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000420558556 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12937 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003281692706 + 0.003231248932 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12937

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12937
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12937 BstLean.Part154.csC) (piBar (rhoBar 12937 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12937 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12937 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12937 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12937 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12937 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12937 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12937 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12937 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12937 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12937 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12937 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12937 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12937 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12937 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051996157341 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12937) ≤ 0.010499628781 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12937 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035476828849)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010499628781 + 2 * 0.737676 / 12937) := by gcongr
    _ ≤ (0.051996157341 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12937 12 ≤ 0.0015 := by
  exact BstLean.Part269.S23.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12937

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12937
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560514089788 : ℝ) ≤ plow 12937 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12937) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052484698396)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354216328) : eMP 12937 0.011 xi bn ≤ 0.001166165126 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12937 : ℝ) * (1 - 0.011))) ≤ 0.000576639049 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001354216328 / (12937 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000576639049 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000576639049 : ℝ) + 3.141593 * 0.052484698396 / (12937 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001166165126 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052484698396)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354216328) : PiBarMP 12937 12 0.011 xi bn ≤ 0.159752191398 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12937 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036799678369 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.113628710248 : ℝ) ≤ √((12937 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.740933704625 : ℝ) ≤ √(12937 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12937) ≤ 0.122492473106 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036799678369 + 0.052484698396 * 1.772454 / (2 * (113.113628710248 : ℝ))) * (1 + 0.001166165126) +
        8 / (12937 * 113.740933704625) + 0.122492473106 := by gcongr
    _ ≤ (0.159752191398 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052484698396)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354216328) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281091548819) :
    parallelOracle 12937 0.011 xi bn cd ≤ 0.160724041195 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12937 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12937 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560514089788 : ℝ) ≤ plow 12937 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.740933704625 : ℝ) ≤ √(12937 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281091548819 : ℝ) / (2 * 0.560514089788 * 113.740933704625)) * 0.159752191398 +
        0.281091548819 ^ 2 / (2 * 0.560514089788 * 113.740933704625) := by gcongr
    _ ≤ (0.160724041195 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052484698396) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001354216328)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281091548819) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12937 12937 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560514089788 : ℝ) ≤ plow 12937 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.740933704625 : ℝ) ≤ √(12937 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12937 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12937 Θ 1.22 ≤ 0.011658955636 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.740933704625 := by gcongr <;> linarith
      _ ≤ (0.011658955636 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12937 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12937 12937 0.011 ≤ 0.008404071698 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12937 12937 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12937 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12937 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12937 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12937 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160724041195 + 0.011658955636 + (0.008404071698 : ℝ) *
        (1 + 2 * (0.281091548819 + 0.011658955636) / (0.560514089788 * 113.740933704625))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12937]

end BstLean.Part269.N12937

/-! The original eight local profiles supply actual 12937 moment certificates. -/
namespace BstLean.Part269.N12937
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12937 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12937 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12937 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052484698396 ∧
    0 ≤ bN 12937 BstLean.Part154.csC (groupTheta g) ∧ bN 12937 BstLean.Part154.csC (groupTheta g) ≤ 0.001354216328 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12937 12937 0.011
      (momentAllowance 12937 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12937 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12937 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12937 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12937 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12937 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229095391478 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12937 0.011
      (momentAllowance 12937 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12937 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12937
/-! The actual computed-centre upper energy formula at 12937. -/
namespace BstLean.Part269.N12937
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12937

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12937
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12937)
open BstLean.Part268 (cell12937)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084827275461
  | 2 => 0.085758457696
  | 3 => 0.086686193136
  | 4 => 0.087611527740
  | 5 => 0.088535737805
  | 6 => 0.089460365581
  | 7 => 0.090387258488
  | 8 => 0.091318612057
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12937 12937 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12937 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003284487036 + 0.003234353889 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S23.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S23.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12937

/-! Actual upper energy certificates on all 43 source endpoints at 12937. -/
namespace BstLean.Part269.N12937
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12937)
open BstLean.Part268 (cell12937)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12937 (gMinus 12937) (1 - (cell12937 i).lower) ≤ 1 ∧
    energyUpper 12937 (gMinus 12937) (BstLean.Part211.gPlus 12937)
      (finiteEnergy 12937 12937 0.011) (1 - (cell12937 i).lower) ≤
      (cell12937 i).energy := by
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
      have E := BstLean.Part269.S23.uniformEnergy10 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨10,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy11 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨11,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy12 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨12,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy13 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨13,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy14 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨14,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy15 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨15,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy16 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨16,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy17 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨17,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy18 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨18,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy19 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨19,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy20 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨20,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy21 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨21,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy22 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨22,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy23 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨23,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy24 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨24,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy25 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨25,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy26 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨26,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy27 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨27,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy28 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨28,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy29 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨29,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy30 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨30,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy31 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨31,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy32 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨32,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy33 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨33,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy34 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨34,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy35 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨35,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy36 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨36,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy37 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨37,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy38 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨38,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy39 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨39,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy40 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨40,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy41 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨41,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy42 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨42,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy43 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨43,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy44 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨44,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy45 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨45,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy46 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨46,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy47 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨47,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy48 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨48,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy49 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨49,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy50 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨50,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy51 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨51,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S23.uniformEnergy52 (n := 12937) (by norm_num)
        (q := 1 - (cell12937 ⟨52,by decide⟩).lower)
        (by norm_num [cell12937]) (by norm_num [cell12937])
      exact ⟨E.1,E.2.trans (by norm_num [cell12937])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12937

/-! Source-cell containment and simple scalar guards at 12937. -/
namespace BstLean.Part269.N12937
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12937)
open BstLean.Part268 (cell12937)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12937 ⟨10,by decide⟩).lower ∧ (cell12937 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12937 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12937 ⟨11,by decide⟩).lower ∧ (cell12937 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12937 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12937 ⟨12,by decide⟩).lower ∧ (cell12937 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12937 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12937 ⟨13,by decide⟩).lower ∧ (cell12937 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12937 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12937 ⟨14,by decide⟩).lower ∧ (cell12937 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12937 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12937 ⟨15,by decide⟩).lower ∧ (cell12937 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12937 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12937 ⟨16,by decide⟩).lower ∧ (cell12937 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12937 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12937 ⟨17,by decide⟩).lower ∧ (cell12937 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12937 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12937 ⟨18,by decide⟩).lower ∧ (cell12937 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12937 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12937 ⟨19,by decide⟩).lower ∧ (cell12937 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12937 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12937 ⟨20,by decide⟩).lower ∧ (cell12937 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12937 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12937 ⟨21,by decide⟩).lower ∧ (cell12937 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12937 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12937 ⟨22,by decide⟩).lower ∧ (cell12937 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12937 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12937 ⟨23,by decide⟩).lower ∧ (cell12937 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12937 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12937 ⟨24,by decide⟩).lower ∧ (cell12937 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12937 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12937 ⟨25,by decide⟩).lower ∧ (cell12937 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12937 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12937 ⟨26,by decide⟩).lower ∧ (cell12937 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12937 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12937 ⟨27,by decide⟩).lower ∧ (cell12937 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12937 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12937 ⟨28,by decide⟩).lower ∧ (cell12937 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12937 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12937 ⟨29,by decide⟩).lower ∧ (cell12937 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12937 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12937 ⟨30,by decide⟩).lower ∧ (cell12937 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12937 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12937 ⟨31,by decide⟩).lower ∧ (cell12937 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12937 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12937 ⟨32,by decide⟩).lower ∧ (cell12937 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12937 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12937 ⟨33,by decide⟩).lower ∧ (cell12937 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12937 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12937 ⟨34,by decide⟩).lower ∧ (cell12937 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12937 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12937 ⟨35,by decide⟩).lower ∧ (cell12937 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12937 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12937 ⟨36,by decide⟩).lower ∧ (cell12937 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12937 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12937 ⟨37,by decide⟩).lower ∧ (cell12937 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12937 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12937 ⟨38,by decide⟩).lower ∧ (cell12937 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12937 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12937 ⟨39,by decide⟩).lower ∧ (cell12937 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12937 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12937 ⟨40,by decide⟩).lower ∧ (cell12937 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12937 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12937 ⟨41,by decide⟩).lower ∧ (cell12937 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12937 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12937 ⟨42,by decide⟩).lower ∧ (cell12937 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12937 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12937 ⟨43,by decide⟩).lower ∧ (cell12937 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12937 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12937 ⟨44,by decide⟩).lower ∧ (cell12937 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12937 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12937 ⟨45,by decide⟩).lower ∧ (cell12937 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12937 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12937 ⟨46,by decide⟩).lower ∧ (cell12937 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12937 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12937 ⟨47,by decide⟩).lower ∧ (cell12937 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12937 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12937 ⟨48,by decide⟩).lower ∧ (cell12937 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12937 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12937 ⟨49,by decide⟩).lower ∧ (cell12937 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12937 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12937 ⟨50,by decide⟩).lower ∧ (cell12937 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12937 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12937 ⟨51,by decide⟩).lower ∧ (cell12937 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12937 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12937 ⟨52,by decide⟩).lower ∧ (cell12937 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12937 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12937 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12937 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12937,cell12937,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12937 i).lower ∧
    (cell12937 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12937 i).upper ≤ (0.532 : ℝ) ∧
    (cell12937 i).centre ≤ (0.1 : ℝ) ∧ (cell12937 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12937 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12937 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12937

/-! The local source numeric instances at 12937 have no network premises. -/
namespace BstLean.Part269.N12937
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12937)
open BstLean.Part268 (cell12937)

noncomputable def sourceNumerics12937 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12937 (cell12937 i)
      scalarRow12937.M scalarRow12937.H scalarRow12937.xi := by
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
    energy_allowance := scalarRow12937.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12937]
    centre_nonneg := (scalarRow12937.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D23.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12937])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12937