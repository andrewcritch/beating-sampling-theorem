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
/-! Actual 12375 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12375
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12375 ≤ (1.036280558322 : ℝ) := by
  have hr : (111.242977306434 : ℝ) ≤ √(12375 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.242977306434 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12375 12375 (11 / 1000) ≤
    (0.008592786248 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12375) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.242977306434 : ℝ) ≤ √(12375 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12375)
  have hdiv : K / √(12375 : ℝ) ≤ K / 111.242977306434 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.242977306434 ≤ (0.008592786248 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12375.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12375 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12375 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12375 := gPlus_lower 12375
end BstLean.Part269.N12375

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12375
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036280558321 : ℝ) ≤ wn 12375 := by
  have hn : √(12375 : ℝ) ≤ 111.242977306435 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12375 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.242977306435 ≤ 2 / √(12375 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258613549 : ℝ) ≤ rhoBar 12375 BstLean.Part154.csC ∧
    rhoBar 12375 BstLean.Part154.csC ≤ 0.000258613949 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036280558321 : ℝ) / (1.295212 * 12375) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036280558322 : ℝ) / (1.29521 * 12375) := by gcongr
      _ ≤ (0.000258613949 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12375 BstLean.Part154.csC) ≤ 0.001034522678 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12375 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12375 BstLean.Part154.csC) (piBar (rhoBar 12375 BstLean.Part154.csC)) ≤ 0.000197531325 ∧
    cc1 (rhoBar 12375 BstLean.Part154.csC) (piBar (rhoBar 12375 BstLean.Part154.csC)) ≤ 0.000125690443 ∧
    cc2 (rhoBar 12375 BstLean.Part154.csC) ≤ 0.000072964204 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12375 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12375 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12375 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12375 BstLean.Part154.csC * nuR (rhoBar 12375 BstLean.Part154.csC)) ≤ 0.000517244619 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258613949 : ℝ) * 0.001034522678 := by gcongr
      _ ≤ (0.000517244619 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12375 BstLean.Part154.csC) * nuR (rhoBar 12375 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001034522678 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12375 BstLean.Part154.csC) * rhoBar 12375 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258613949 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258613949 / 2 + 0.399 * 0.001034522678 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197531325 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517244619 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125690443 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258613949 / 1.414213562 := by gcongr
      _ ≤ (0.000072964204 : ℝ) := by norm_num

end BstLean.Part269.N12375

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12375
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12375 BstLean.Part154.csC) (piBar (rhoBar 12375 BstLean.Part154.csC)) ≤ 1.68503E-7 := by
  have hr0 : 0 ≤ rhoBar 12375 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12375 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12375 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12375 BstLean.Part154.csC) (piBar (rhoBar 12375 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12375 BstLean.Part154.csC) (piBar (rhoBar 12375 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12375 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197531325 : ℝ) ^ 2 + 0.000125690443 ^ 2 + 3 * 0.000072964204 ^ 2 +
        2 * 0.797885 * 0.000197531325 * 0.000125690443 + 2 * 0.000197531325 * 0.000072964204 +
        4 * 0.797885 * 0.000125690443 * 0.000072964204 := by gcongr
    _ ≤ (1.68503E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12375 BstLean.Part154.csC Θ ≤ 0.002700807960 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12375 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12375 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12375 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12375 BstLean.Part154.csC) (piBar (rhoBar 12375 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12375 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036280558322 * 1.68503E-7 / (0.000258613549 : ℝ) := by gcongr
    _ ≤ 0.002700807960 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12375 BstLean.Part154.csC Θ ≤ 0.002998049004 + 0.000682447899 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12375 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12375 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12375 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036280558322 : ℝ) * ((2 * Θ * 0.000258613949 +
        (6863 / 10000) * 0.000258613949 * 12375 * 0.001034522678) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002998049004 + 0.000682447899 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12375 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12375 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12375 0.011 Θ ∧ gammaRatio 12375 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12375 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036280558322 : ℝ) * 0.525 / ((1 - 0.011) * 12375) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12375 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12375 0.011 Θ) :=
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
    badAllowance 12375 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12375 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12375 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12375 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12375 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12375 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12375 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12375 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12375 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12375 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12375 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036280558322 : ℝ) * 12375 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12375 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004098049004 + 0.003383255859 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12375

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12375
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12375 BstLean.Part154.csC) (piBar (rhoBar 12375 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12375 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12375 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12375 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12375 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12375 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12375 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12375 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12375 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12375 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12375 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12375 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12375 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12375 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12375 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053176555851 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12375) ≤ 0.010735397506 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12375 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036280558322)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010735397506 + 2 * 0.737676 / 12375) := by gcongr
    _ ≤ (0.053176555851 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12375 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12375

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12375
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488484832 : ℝ) ≤ plow 12375 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12375) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053380858330)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417924179) : eMP 12375 0.011 xi bn ≤ 0.001220295064 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12375 : ℝ) * (1 - 0.011))) ≤ 0.000603296374 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001417924179 / (12375 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603296374 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603296374 : ℝ) + 3.141593 * 0.053380858330 / (12375 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001220295064 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053380858330)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417924179) : PiBarMP 12375 12 0.011 xi bn ≤ 0.163378275938 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12375 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037655334005 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.629449063077 : ℝ) ≤ √((12375 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.242977306434 : ℝ) ≤ √(12375 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12375) ≤ 0.125243036461 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037655334005 + 0.053380858330 * 1.772454 / (2 * (110.629449063077 : ℝ))) * (1 + 0.001220295064) +
        8 / (12375 * 111.242977306434) + 0.125243036461 := by gcongr
    _ ≤ (0.163378275938 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053380858330)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417924179) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284219535251) :
    parallelOracle 12375 0.011 xi bn cd ≤ 0.164398446025 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12375 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12375 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488484832 : ℝ) ≤ plow 12375 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.242977306434 : ℝ) ≤ √(12375 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284219535251 : ℝ) / (2 * 0.560488484832 * 111.242977306434)) * 0.163378275938 +
        0.284219535251 ^ 2 / (2 * 0.560488484832 * 111.242977306434) := by gcongr
    _ ≤ (0.164398446025 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053380858330) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417924179)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284219535251) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12375 12375 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488484832 : ℝ) ≤ plow 12375 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.242977306434 : ℝ) ≤ √(12375 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12375 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12375 Θ 1.22 ≤ 0.011920756997 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.242977306434 := by gcongr <;> linarith
      _ ≤ (0.011920756997 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12375 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12375 12375 0.011 ≤ 0.008592786248 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12375 12375 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12375 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12375 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12375 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12375 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164398446025 + 0.011920756997 + (0.008592786248 : ℝ) *
        (1 + 2 * (0.284219535251 + 0.011920756997) / (0.560488484832 * 111.242977306434))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12375]

end BstLean.Part269.N12375

/-! The original eight local profiles supply actual 12375 moment certificates. -/
namespace BstLean.Part269.N12375
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12375 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12375 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12375 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053380858330 ∧
    0 ≤ bN 12375 BstLean.Part154.csC (groupTheta g) ∧ bN 12375 BstLean.Part154.csC (groupTheta g) ≤ 0.001417924179 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12375 12375 0.011
      (momentAllowance 12375 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12375 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12375 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12375 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12375 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12375 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231042979400 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12375 0.011
      (momentAllowance 12375 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12375 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12375
/-! The actual computed-centre upper energy formula at 12375. -/
namespace BstLean.Part269.N12375
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12375

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12375
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12375)
open BstLean.Part268 (cell12375)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086502299449
  | 2 => 0.087465181410
  | 3 => 0.088429380634
  | 4 => 0.089397027929
  | 5 => 0.090370673738
  | 6 => 0.091353346859
  | 7 => 0.092348618055
  | 8 => 0.093360668476
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12375 12375 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12375 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12375

/-! Actual upper energy certificates on all 43 source endpoints at 12375. -/
namespace BstLean.Part269.N12375
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12375)
open BstLean.Part268 (cell12375)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12375 (gMinus 12375) (1 - (cell12375 i).lower) ≤ 1 ∧
    energyUpper 12375 (gMinus 12375) (BstLean.Part211.gPlus 12375)
      (finiteEnergy 12375 12375 0.011) (1 - (cell12375 i).lower) ≤
      (cell12375 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨10,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨11,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨12,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨13,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨14,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨15,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨16,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨17,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨18,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨19,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨20,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨21,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨22,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨23,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨24,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨25,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨26,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨27,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨28,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨29,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨30,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨31,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨32,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨33,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨34,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨35,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨36,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨37,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨38,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨39,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨40,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨41,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨42,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨43,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨44,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨45,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨46,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨47,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨48,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨49,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨50,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨51,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12375) (by norm_num)
        (q := 1 - (cell12375 ⟨52,by decide⟩).lower)
        (by norm_num [cell12375]) (by norm_num [cell12375])
      exact ⟨E.1,E.2.trans (by norm_num [cell12375])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12375

/-! Source-cell containment and simple scalar guards at 12375. -/
namespace BstLean.Part269.N12375
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12375)
open BstLean.Part268 (cell12375)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12375 ⟨10,by decide⟩).lower ∧ (cell12375 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12375 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12375 ⟨11,by decide⟩).lower ∧ (cell12375 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12375 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12375 ⟨12,by decide⟩).lower ∧ (cell12375 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12375 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12375 ⟨13,by decide⟩).lower ∧ (cell12375 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12375 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12375 ⟨14,by decide⟩).lower ∧ (cell12375 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12375 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12375 ⟨15,by decide⟩).lower ∧ (cell12375 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12375 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12375 ⟨16,by decide⟩).lower ∧ (cell12375 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12375 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12375 ⟨17,by decide⟩).lower ∧ (cell12375 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12375 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12375 ⟨18,by decide⟩).lower ∧ (cell12375 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12375 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12375 ⟨19,by decide⟩).lower ∧ (cell12375 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12375 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12375 ⟨20,by decide⟩).lower ∧ (cell12375 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12375 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12375 ⟨21,by decide⟩).lower ∧ (cell12375 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12375 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12375 ⟨22,by decide⟩).lower ∧ (cell12375 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12375 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12375 ⟨23,by decide⟩).lower ∧ (cell12375 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12375 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12375 ⟨24,by decide⟩).lower ∧ (cell12375 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12375 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12375 ⟨25,by decide⟩).lower ∧ (cell12375 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12375 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12375 ⟨26,by decide⟩).lower ∧ (cell12375 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12375 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12375 ⟨27,by decide⟩).lower ∧ (cell12375 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12375 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12375 ⟨28,by decide⟩).lower ∧ (cell12375 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12375 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12375 ⟨29,by decide⟩).lower ∧ (cell12375 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12375 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12375 ⟨30,by decide⟩).lower ∧ (cell12375 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12375 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12375 ⟨31,by decide⟩).lower ∧ (cell12375 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12375 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12375 ⟨32,by decide⟩).lower ∧ (cell12375 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12375 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12375 ⟨33,by decide⟩).lower ∧ (cell12375 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12375 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12375 ⟨34,by decide⟩).lower ∧ (cell12375 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12375 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12375 ⟨35,by decide⟩).lower ∧ (cell12375 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12375 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12375 ⟨36,by decide⟩).lower ∧ (cell12375 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12375 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12375 ⟨37,by decide⟩).lower ∧ (cell12375 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12375 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12375 ⟨38,by decide⟩).lower ∧ (cell12375 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12375 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12375 ⟨39,by decide⟩).lower ∧ (cell12375 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12375 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12375 ⟨40,by decide⟩).lower ∧ (cell12375 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12375 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12375 ⟨41,by decide⟩).lower ∧ (cell12375 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12375 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12375 ⟨42,by decide⟩).lower ∧ (cell12375 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12375 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12375 ⟨43,by decide⟩).lower ∧ (cell12375 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12375 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12375 ⟨44,by decide⟩).lower ∧ (cell12375 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12375 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12375 ⟨45,by decide⟩).lower ∧ (cell12375 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12375 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12375 ⟨46,by decide⟩).lower ∧ (cell12375 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12375 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12375 ⟨47,by decide⟩).lower ∧ (cell12375 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12375 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12375 ⟨48,by decide⟩).lower ∧ (cell12375 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12375 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12375 ⟨49,by decide⟩).lower ∧ (cell12375 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12375 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12375 ⟨50,by decide⟩).lower ∧ (cell12375 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12375 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12375 ⟨51,by decide⟩).lower ∧ (cell12375 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12375 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12375 ⟨52,by decide⟩).lower ∧ (cell12375 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12375 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12375 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12375 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12375,cell12375,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12375 i).lower ∧
    (cell12375 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12375 i).upper ≤ (0.532 : ℝ) ∧
    (cell12375 i).centre ≤ (0.1 : ℝ) ∧ (cell12375 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12375 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12375 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12375

/-! The local source numeric instances at 12375 have no network premises. -/
namespace BstLean.Part269.N12375
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12375)
open BstLean.Part268 (cell12375)

noncomputable def sourceNumerics12375 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12375 (cell12375 i)
      scalarRow12375.M scalarRow12375.H scalarRow12375.xi := by
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
    energy_allowance := scalarRow12375.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12375]
    centre_nonneg := (scalarRow12375.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12375])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12375
/-! Actual 12376 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12376
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12376 ≤ (1.036279079471 : ℝ) := by
  have hr : (111.247471881387 : ℝ) ≤ √(12376 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.247471881387 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12376 12376 (11 / 1000) ≤
    (0.008592439083 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12376) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.247471881387 : ℝ) ≤ √(12376 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12376)
  have hdiv : K / √(12376 : ℝ) ≤ K / 111.247471881387 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.247471881387 ≤ (0.008592439083 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12376.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12376 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12376 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12376 := gPlus_lower 12376
end BstLean.Part269.N12376

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12376
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036279079470 : ℝ) ≤ wn 12376 := by
  have hn : √(12376 : ℝ) ≤ 111.247471881388 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12376 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.247471881388 ≤ 2 / √(12376 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258592283 : ℝ) ≤ rhoBar 12376 BstLean.Part154.csC ∧
    rhoBar 12376 BstLean.Part154.csC ≤ 0.000258592684 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036279079470 : ℝ) / (1.295212 * 12376) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036279079471 : ℝ) / (1.29521 * 12376) := by gcongr
      _ ≤ (0.000258592684 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12376 BstLean.Part154.csC) ≤ 0.001034437607 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12376 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12376 BstLean.Part154.csC) (piBar (rhoBar 12376 BstLean.Part154.csC)) ≤ 0.000197515081 ∧
    cc1 (rhoBar 12376 BstLean.Part154.csC) (piBar (rhoBar 12376 BstLean.Part154.csC)) ≤ 0.000125680107 ∧
    cc2 (rhoBar 12376 BstLean.Part154.csC) ≤ 0.000072958204 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12376 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12376 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12376 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12376 BstLean.Part154.csC * nuR (rhoBar 12376 BstLean.Part154.csC)) ≤ 0.000517202086 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258592684 : ℝ) * 0.001034437607 := by gcongr
      _ ≤ (0.000517202086 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12376 BstLean.Part154.csC) * nuR (rhoBar 12376 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001034437607 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12376 BstLean.Part154.csC) * rhoBar 12376 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258592684 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258592684 / 2 + 0.399 * 0.001034437607 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197515081 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517202086 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125680107 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258592684 / 1.414213562 := by gcongr
      _ ≤ (0.000072958204 : ℝ) := by norm_num

end BstLean.Part269.N12376

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12376
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12376 BstLean.Part154.csC) (piBar (rhoBar 12376 BstLean.Part154.csC)) ≤ 1.68475E-7 := by
  have hr0 : 0 ≤ rhoBar 12376 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12376 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12376 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12376 BstLean.Part154.csC) (piBar (rhoBar 12376 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12376 BstLean.Part154.csC) (piBar (rhoBar 12376 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12376 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197515081 : ℝ) ^ 2 + 0.000125680107 ^ 2 + 3 * 0.000072958204 ^ 2 +
        2 * 0.797885 * 0.000197515081 * 0.000125680107 + 2 * 0.000197515081 * 0.000072958204 +
        4 * 0.797885 * 0.000125680107 * 0.000072958204 := by gcongr
    _ ≤ (1.68475E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12376 BstLean.Part154.csC Θ ≤ 0.002700577386 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12376 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12376 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12376 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12376 BstLean.Part154.csC) (piBar (rhoBar 12376 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12376 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036279079471 * 1.68475E-7 / (0.000258592283 : ℝ) := by gcongr
    _ ≤ 0.002700577386 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12376 BstLean.Part154.csC Θ ≤ 0.002997793917 + 0.000682390810 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12376 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12376 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12376 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036279079471 : ℝ) * ((2 * Θ * 0.000258592684 +
        (6863 / 10000) * 0.000258592684 * 12376 * 0.001034437607) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002997793917 + 0.000682390810 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12376 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12376 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12376 0.011 Θ ∧ gammaRatio 12376 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12376 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036279079471 : ℝ) * 0.525 / ((1 - 0.011) * 12376) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12376 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12376 0.011 Θ) :=
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
    badAllowance 12376 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12376 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12376 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12376 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12376 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12376 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12376 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12376 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12376 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12376 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12376 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036279079471 : ℝ) * 12376 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12376 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004097793917 + 0.003382968196 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12376

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12376
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12376 BstLean.Part154.csC) (piBar (rhoBar 12376 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12376 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12376 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12376 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12376 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12376 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12376 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12376 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12376 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12376 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12376 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12376 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12376 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12376 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12376 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053174383839 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12376) ≤ 0.010734963779 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12376 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036279079471)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010734963779 + 2 * 0.737676 / 12376) := by gcongr
    _ ≤ (0.053174383839 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12376 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12376

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12376
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488532457 : ℝ) ≤ plow 12376 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12376) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053380452220)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417803128) : eMP 12376 0.011 xi bn ≤ 0.001220193601 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12376 : ℝ) * (1 - 0.011))) ≤ 0.000603246248 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001417803128 / (12376 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603246248 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603246248 : ℝ) + 3.141593 * 0.053380452220 / (12376 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001220193601 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053380452220)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417803128) : PiBarMP 12376 12 0.011 xi bn ≤ 0.163371581447 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12376 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037653726616 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.633918849510 : ℝ) ≤ √((12376 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.247471881387 : ℝ) ≤ √(12376 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12376) ≤ 0.125237976443 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037653726616 + 0.053380452220 * 1.772454 / (2 * (110.633918849510 : ℝ))) * (1 + 0.001220193601) +
        8 / (12376 * 111.247471881387) + 0.125237976443 := by gcongr
    _ ≤ (0.163371581447 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053380452220)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417803128) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284216484375) :
    parallelOracle 12376 0.011 xi bn cd ≤ 0.164391677070 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12376 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12376 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488532457 : ℝ) ≤ plow 12376 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.247471881387 : ℝ) ≤ √(12376 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284216484375 : ℝ) / (2 * 0.560488532457 * 111.247471881387)) * 0.163371581447 +
        0.284216484375 ^ 2 / (2 * 0.560488532457 * 111.247471881387) := by gcongr
    _ ≤ (0.164391677070 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053380452220) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417803128)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284216484375) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12376 12376 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488532457 : ℝ) ≤ plow 12376 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.247471881387 : ℝ) ≤ √(12376 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12376 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12376 Θ 1.22 ≤ 0.011920275379 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.247471881387 := by gcongr <;> linarith
      _ ≤ (0.011920275379 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12376 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12376 12376 0.011 ≤ 0.008592439083 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12376 12376 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12376 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12376 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12376 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12376 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164391677070 + 0.011920275379 + (0.008592439083 : ℝ) *
        (1 + 2 * (0.284216484375 + 0.011920275379) / (0.560488532457 * 111.247471881387))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12376]

end BstLean.Part269.N12376

/-! The original eight local profiles supply actual 12376 moment certificates. -/
namespace BstLean.Part269.N12376
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12376 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12376 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12376 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053380452220 ∧
    0 ≤ bN 12376 BstLean.Part154.csC (groupTheta g) ∧ bN 12376 BstLean.Part154.csC (groupTheta g) ≤ 0.001417803128 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12376 12376 0.011
      (momentAllowance 12376 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12376 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12376 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12376 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12376 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12376 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231042100536 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12376 0.011
      (momentAllowance 12376 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12376 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12376
/-! The actual computed-centre upper energy formula at 12376. -/
namespace BstLean.Part269.N12376
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12376

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12376
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12376)
open BstLean.Part268 (cell12376)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086498964585
  | 2 => 0.087461774993
  | 3 => 0.088425890642
  | 4 => 0.089393439706
  | 5 => 0.090366969551
  | 6 => 0.091349505405
  | 7 => 0.092344613917
  | 8 => 0.093356471521
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12376 12376 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12376 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12376

/-! Actual upper energy certificates on all 43 source endpoints at 12376. -/
namespace BstLean.Part269.N12376
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12376)
open BstLean.Part268 (cell12376)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12376 (gMinus 12376) (1 - (cell12376 i).lower) ≤ 1 ∧
    energyUpper 12376 (gMinus 12376) (BstLean.Part211.gPlus 12376)
      (finiteEnergy 12376 12376 0.011) (1 - (cell12376 i).lower) ≤
      (cell12376 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨10,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨11,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨12,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨13,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨14,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨15,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨16,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨17,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨18,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨19,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨20,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨21,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨22,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨23,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨24,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨25,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨26,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨27,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨28,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨29,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨30,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨31,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨32,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨33,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨34,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨35,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨36,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨37,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨38,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨39,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨40,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨41,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨42,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨43,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨44,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨45,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨46,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨47,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨48,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨49,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨50,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨51,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12376) (by norm_num)
        (q := 1 - (cell12376 ⟨52,by decide⟩).lower)
        (by norm_num [cell12376]) (by norm_num [cell12376])
      exact ⟨E.1,E.2.trans (by norm_num [cell12376])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12376

/-! Source-cell containment and simple scalar guards at 12376. -/
namespace BstLean.Part269.N12376
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12376)
open BstLean.Part268 (cell12376)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12376 ⟨10,by decide⟩).lower ∧ (cell12376 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12376 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12376 ⟨11,by decide⟩).lower ∧ (cell12376 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12376 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12376 ⟨12,by decide⟩).lower ∧ (cell12376 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12376 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12376 ⟨13,by decide⟩).lower ∧ (cell12376 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12376 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12376 ⟨14,by decide⟩).lower ∧ (cell12376 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12376 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12376 ⟨15,by decide⟩).lower ∧ (cell12376 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12376 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12376 ⟨16,by decide⟩).lower ∧ (cell12376 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12376 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12376 ⟨17,by decide⟩).lower ∧ (cell12376 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12376 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12376 ⟨18,by decide⟩).lower ∧ (cell12376 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12376 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12376 ⟨19,by decide⟩).lower ∧ (cell12376 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12376 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12376 ⟨20,by decide⟩).lower ∧ (cell12376 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12376 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12376 ⟨21,by decide⟩).lower ∧ (cell12376 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12376 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12376 ⟨22,by decide⟩).lower ∧ (cell12376 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12376 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12376 ⟨23,by decide⟩).lower ∧ (cell12376 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12376 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12376 ⟨24,by decide⟩).lower ∧ (cell12376 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12376 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12376 ⟨25,by decide⟩).lower ∧ (cell12376 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12376 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12376 ⟨26,by decide⟩).lower ∧ (cell12376 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12376 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12376 ⟨27,by decide⟩).lower ∧ (cell12376 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12376 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12376 ⟨28,by decide⟩).lower ∧ (cell12376 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12376 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12376 ⟨29,by decide⟩).lower ∧ (cell12376 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12376 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12376 ⟨30,by decide⟩).lower ∧ (cell12376 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12376 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12376 ⟨31,by decide⟩).lower ∧ (cell12376 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12376 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12376 ⟨32,by decide⟩).lower ∧ (cell12376 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12376 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12376 ⟨33,by decide⟩).lower ∧ (cell12376 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12376 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12376 ⟨34,by decide⟩).lower ∧ (cell12376 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12376 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12376 ⟨35,by decide⟩).lower ∧ (cell12376 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12376 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12376 ⟨36,by decide⟩).lower ∧ (cell12376 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12376 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12376 ⟨37,by decide⟩).lower ∧ (cell12376 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12376 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12376 ⟨38,by decide⟩).lower ∧ (cell12376 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12376 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12376 ⟨39,by decide⟩).lower ∧ (cell12376 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12376 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12376 ⟨40,by decide⟩).lower ∧ (cell12376 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12376 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12376 ⟨41,by decide⟩).lower ∧ (cell12376 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12376 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12376 ⟨42,by decide⟩).lower ∧ (cell12376 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12376 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12376 ⟨43,by decide⟩).lower ∧ (cell12376 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12376 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12376 ⟨44,by decide⟩).lower ∧ (cell12376 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12376 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12376 ⟨45,by decide⟩).lower ∧ (cell12376 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12376 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12376 ⟨46,by decide⟩).lower ∧ (cell12376 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12376 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12376 ⟨47,by decide⟩).lower ∧ (cell12376 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12376 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12376 ⟨48,by decide⟩).lower ∧ (cell12376 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12376 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12376 ⟨49,by decide⟩).lower ∧ (cell12376 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12376 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12376 ⟨50,by decide⟩).lower ∧ (cell12376 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12376 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12376 ⟨51,by decide⟩).lower ∧ (cell12376 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12376 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12376 ⟨52,by decide⟩).lower ∧ (cell12376 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12376 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12376 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12376 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12376,cell12376,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12376 i).lower ∧
    (cell12376 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12376 i).upper ≤ (0.532 : ℝ) ∧
    (cell12376 i).centre ≤ (0.1 : ℝ) ∧ (cell12376 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12376 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12376 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12376

/-! The local source numeric instances at 12376 have no network premises. -/
namespace BstLean.Part269.N12376
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12376)
open BstLean.Part268 (cell12376)

noncomputable def sourceNumerics12376 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12376 (cell12376 i)
      scalarRow12376.M scalarRow12376.H scalarRow12376.xi := by
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
    energy_allowance := scalarRow12376.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12376]
    centre_nonneg := (scalarRow12376.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12376])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12376
/-! Actual 12377 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12377
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12377 ≤ (1.036277600800 : ℝ) := by
  have hr : (111.251966274758 : ℝ) ≤ √(12377 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.251966274758 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12377 12377 (11 / 1000) ≤
    (0.008592091961 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12377) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.251966274758 : ℝ) ≤ √(12377 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12377)
  have hdiv : K / √(12377 : ℝ) ≤ K / 111.251966274758 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.251966274758 ≤ (0.008592091961 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12377.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12377 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12377 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12377 := gPlus_lower 12377
end BstLean.Part269.N12377

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12377
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036277600799 : ℝ) ≤ wn 12377 := by
  have hn : √(12377 : ℝ) ≤ 111.251966274759 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12377 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.251966274759 ≤ 2 / √(12377 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258571021 : ℝ) ≤ rhoBar 12377 BstLean.Part154.csC ∧
    rhoBar 12377 BstLean.Part154.csC ≤ 0.000258571422 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036277600799 : ℝ) / (1.295212 * 12377) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036277600800 : ℝ) / (1.29521 * 12377) := by gcongr
      _ ≤ (0.000258571422 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12377 BstLean.Part154.csC) ≤ 0.001034352548 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12377 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12377 BstLean.Part154.csC) (piBar (rhoBar 12377 BstLean.Part154.csC)) ≤ 0.000197498841 ∧
    cc1 (rhoBar 12377 BstLean.Part154.csC) (piBar (rhoBar 12377 BstLean.Part154.csC)) ≤ 0.000125669773 ∧
    cc2 (rhoBar 12377 BstLean.Part154.csC) ≤ 0.000072952205 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12377 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12377 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12377 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12377 BstLean.Part154.csC * nuR (rhoBar 12377 BstLean.Part154.csC)) ≤ 0.000517159559 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258571422 : ℝ) * 0.001034352548 := by gcongr
      _ ≤ (0.000517159559 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12377 BstLean.Part154.csC) * nuR (rhoBar 12377 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001034352548 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12377 BstLean.Part154.csC) * rhoBar 12377 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258571422 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258571422 / 2 + 0.399 * 0.001034352548 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197498841 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517159559 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125669773 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258571422 / 1.414213562 := by gcongr
      _ ≤ (0.000072952205 : ℝ) := by norm_num

end BstLean.Part269.N12377

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12377
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12377 BstLean.Part154.csC) (piBar (rhoBar 12377 BstLean.Part154.csC)) ≤ 1.68447E-7 := by
  have hr0 : 0 ≤ rhoBar 12377 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12377 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12377 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12377 BstLean.Part154.csC) (piBar (rhoBar 12377 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12377 BstLean.Part154.csC) (piBar (rhoBar 12377 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12377 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197498841 : ℝ) ^ 2 + 0.000125669773 ^ 2 + 3 * 0.000072952205 ^ 2 +
        2 * 0.797885 * 0.000197498841 * 0.000125669773 + 2 * 0.000197498841 * 0.000072952205 +
        4 * 0.797885 * 0.000125669773 * 0.000072952205 := by gcongr
    _ ≤ (1.68447E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12377 BstLean.Part154.csC Θ ≤ 0.002700346735 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12377 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12377 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12377 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12377 BstLean.Part154.csC) (piBar (rhoBar 12377 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12377 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036277600800 * 1.68447E-7 / (0.000258571021 : ℝ) := by gcongr
    _ ≤ 0.002700346735 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12377 BstLean.Part154.csC Θ ≤ 0.002997538862 + 0.000682333729 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12377 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12377 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12377 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036277600800 : ℝ) * ((2 * Θ * 0.000258571422 +
        (6863 / 10000) * 0.000258571422 * 12377 * 0.001034352548) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002997538862 + 0.000682333729 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12377 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12377 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12377 0.011 Θ ∧ gammaRatio 12377 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12377 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036277600800 : ℝ) * 0.525 / ((1 - 0.011) * 12377) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12377 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12377 0.011 Θ) :=
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
    badAllowance 12377 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12377 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12377 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12377 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12377 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12377 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12377 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12377 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12377 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12377 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12377 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036277600800 : ℝ) * 12377 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12377 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004097538862 + 0.003382680464 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12377

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12377
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12377 BstLean.Part154.csC) (piBar (rhoBar 12377 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12377 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12377 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12377 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12377 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12377 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12377 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12377 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12377 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12377 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12377 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12377 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12377 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12377 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12377 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053172212088 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12377) ≤ 0.010734530104 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12377 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036277600800)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010734530104 + 2 * 0.737676 / 12377) := by gcongr
    _ ≤ (0.053172212088 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12377 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12377

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12377
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488580075 : ℝ) ≤ plow 12377 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12377) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053380046106)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417682036) : eMP 12377 0.011 xi bn ≤ 0.001220092130 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12377 : ℝ) * (1 - 0.011))) ≤ 0.000603196118 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001417682036 / (12377 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603196118 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603196118 : ℝ) + 3.141593 * 0.053380046106 / (12377 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001220092130 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053380046106)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417682036) : PiBarMP 12377 12 0.011 xi bn ≤ 0.163364886956 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12377 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037652118613 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.638388455363 : ℝ) ≤ √((12377 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.251966274758 : ℝ) ≤ √(12377 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12377) ≤ 0.125232917038 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037652118613 + 0.053380046106 * 1.772454 / (2 * (110.638388455363 : ℝ))) * (1 + 0.001220092130) +
        8 / (12377 * 111.251966274758) + 0.125232917038 := by gcongr
    _ ≤ (0.163364886956 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053380046106)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417682036) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284213433748) :
    parallelOracle 12377 0.011 xi bn cd ≤ 0.164384908125 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12377 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12377 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488580075 : ℝ) ≤ plow 12377 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.251966274758 : ℝ) ≤ √(12377 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284213433748 : ℝ) / (2 * 0.560488580075 * 111.251966274758)) * 0.163364886956 +
        0.284213433748 ^ 2 / (2 * 0.560488580075 * 111.251966274758) := by gcongr
    _ ≤ (0.164384908125 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053380046106) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417682036)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284213433748) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12377 12377 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488580075 : ℝ) ≤ plow 12377 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.251966274758 : ℝ) ≤ √(12377 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12377 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12377 Θ 1.22 ≤ 0.011919793820 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.251966274758 := by gcongr <;> linarith
      _ ≤ (0.011919793820 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12377 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12377 12377 0.011 ≤ 0.008592091961 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12377 12377 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12377 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12377 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12377 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12377 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164384908125 + 0.011919793820 + (0.008592091961 : ℝ) *
        (1 + 2 * (0.284213433748 + 0.011919793820) / (0.560488580075 * 111.251966274758))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12377]

end BstLean.Part269.N12377

/-! The original eight local profiles supply actual 12377 moment certificates. -/
namespace BstLean.Part269.N12377
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12377 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12377 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12377 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053380046106 ∧
    0 ≤ bN 12377 BstLean.Part154.csC (groupTheta g) ∧ bN 12377 BstLean.Part154.csC (groupTheta g) ≤ 0.001417682036 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12377 12377 0.011
      (momentAllowance 12377 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12377 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12377 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12377 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12377 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12377 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231041221660 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12377 0.011
      (momentAllowance 12377 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12377 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12377
/-! The actual computed-centre upper energy formula at 12377. -/
namespace BstLean.Part269.N12377
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12377

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12377
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12377)
open BstLean.Part268 (cell12377)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086495631247
  | 2 => 0.087458370169
  | 3 => 0.088422402327
  | 4 => 0.089389853264
  | 5 => 0.090363267270
  | 6 => 0.091345666009
  | 7 => 0.092340612018
  | 8 => 0.093352277023
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12377 12377 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12377 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12377

/-! Actual upper energy certificates on all 43 source endpoints at 12377. -/
namespace BstLean.Part269.N12377
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12377)
open BstLean.Part268 (cell12377)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12377 (gMinus 12377) (1 - (cell12377 i).lower) ≤ 1 ∧
    energyUpper 12377 (gMinus 12377) (BstLean.Part211.gPlus 12377)
      (finiteEnergy 12377 12377 0.011) (1 - (cell12377 i).lower) ≤
      (cell12377 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨10,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨11,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨12,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨13,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨14,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨15,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨16,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨17,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨18,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨19,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨20,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨21,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨22,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨23,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨24,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨25,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨26,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨27,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨28,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨29,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨30,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨31,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨32,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨33,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨34,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨35,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨36,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨37,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨38,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨39,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨40,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨41,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨42,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨43,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨44,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨45,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨46,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨47,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨48,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨49,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨50,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨51,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12377) (by norm_num)
        (q := 1 - (cell12377 ⟨52,by decide⟩).lower)
        (by norm_num [cell12377]) (by norm_num [cell12377])
      exact ⟨E.1,E.2.trans (by norm_num [cell12377])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12377

/-! Source-cell containment and simple scalar guards at 12377. -/
namespace BstLean.Part269.N12377
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12377)
open BstLean.Part268 (cell12377)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12377 ⟨10,by decide⟩).lower ∧ (cell12377 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12377 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12377 ⟨11,by decide⟩).lower ∧ (cell12377 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12377 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12377 ⟨12,by decide⟩).lower ∧ (cell12377 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12377 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12377 ⟨13,by decide⟩).lower ∧ (cell12377 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12377 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12377 ⟨14,by decide⟩).lower ∧ (cell12377 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12377 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12377 ⟨15,by decide⟩).lower ∧ (cell12377 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12377 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12377 ⟨16,by decide⟩).lower ∧ (cell12377 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12377 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12377 ⟨17,by decide⟩).lower ∧ (cell12377 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12377 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12377 ⟨18,by decide⟩).lower ∧ (cell12377 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12377 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12377 ⟨19,by decide⟩).lower ∧ (cell12377 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12377 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12377 ⟨20,by decide⟩).lower ∧ (cell12377 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12377 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12377 ⟨21,by decide⟩).lower ∧ (cell12377 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12377 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12377 ⟨22,by decide⟩).lower ∧ (cell12377 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12377 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12377 ⟨23,by decide⟩).lower ∧ (cell12377 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12377 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12377 ⟨24,by decide⟩).lower ∧ (cell12377 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12377 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12377 ⟨25,by decide⟩).lower ∧ (cell12377 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12377 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12377 ⟨26,by decide⟩).lower ∧ (cell12377 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12377 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12377 ⟨27,by decide⟩).lower ∧ (cell12377 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12377 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12377 ⟨28,by decide⟩).lower ∧ (cell12377 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12377 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12377 ⟨29,by decide⟩).lower ∧ (cell12377 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12377 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12377 ⟨30,by decide⟩).lower ∧ (cell12377 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12377 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12377 ⟨31,by decide⟩).lower ∧ (cell12377 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12377 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12377 ⟨32,by decide⟩).lower ∧ (cell12377 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12377 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12377 ⟨33,by decide⟩).lower ∧ (cell12377 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12377 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12377 ⟨34,by decide⟩).lower ∧ (cell12377 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12377 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12377 ⟨35,by decide⟩).lower ∧ (cell12377 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12377 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12377 ⟨36,by decide⟩).lower ∧ (cell12377 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12377 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12377 ⟨37,by decide⟩).lower ∧ (cell12377 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12377 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12377 ⟨38,by decide⟩).lower ∧ (cell12377 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12377 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12377 ⟨39,by decide⟩).lower ∧ (cell12377 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12377 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12377 ⟨40,by decide⟩).lower ∧ (cell12377 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12377 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12377 ⟨41,by decide⟩).lower ∧ (cell12377 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12377 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12377 ⟨42,by decide⟩).lower ∧ (cell12377 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12377 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12377 ⟨43,by decide⟩).lower ∧ (cell12377 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12377 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12377 ⟨44,by decide⟩).lower ∧ (cell12377 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12377 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12377 ⟨45,by decide⟩).lower ∧ (cell12377 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12377 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12377 ⟨46,by decide⟩).lower ∧ (cell12377 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12377 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12377 ⟨47,by decide⟩).lower ∧ (cell12377 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12377 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12377 ⟨48,by decide⟩).lower ∧ (cell12377 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12377 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12377 ⟨49,by decide⟩).lower ∧ (cell12377 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12377 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12377 ⟨50,by decide⟩).lower ∧ (cell12377 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12377 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12377 ⟨51,by decide⟩).lower ∧ (cell12377 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12377 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12377 ⟨52,by decide⟩).lower ∧ (cell12377 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12377 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12377 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12377 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12377,cell12377,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12377 i).lower ∧
    (cell12377 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12377 i).upper ≤ (0.532 : ℝ) ∧
    (cell12377 i).centre ≤ (0.1 : ℝ) ∧ (cell12377 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12377 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12377 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12377

/-! The local source numeric instances at 12377 have no network premises. -/
namespace BstLean.Part269.N12377
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12377)
open BstLean.Part268 (cell12377)

noncomputable def sourceNumerics12377 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12377 (cell12377 i)
      scalarRow12377.M scalarRow12377.H scalarRow12377.xi := by
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
    energy_allowance := scalarRow12377.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12377]
    centre_nonneg := (scalarRow12377.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12377])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12377
/-! Actual 12378 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12378
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12378 ≤ (1.036276122310 : ℝ) := by
  have hr : (111.256460486571 : ℝ) ≤ √(12378 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.256460486571 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12378 12378 (11 / 1000) ≤
    (0.008591744880 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12378) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.256460486571 : ℝ) ≤ √(12378 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12378)
  have hdiv : K / √(12378 : ℝ) ≤ K / 111.256460486571 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.256460486571 ≤ (0.008591744880 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12378.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12378 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12378 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12378 := gPlus_lower 12378
end BstLean.Part269.N12378

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12378
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036276122309 : ℝ) ≤ wn 12378 := by
  have hn : √(12378 : ℝ) ≤ 111.256460486572 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12378 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.256460486572 ≤ 2 / √(12378 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258549763 : ℝ) ≤ rhoBar 12378 BstLean.Part154.csC ∧
    rhoBar 12378 BstLean.Part154.csC ≤ 0.000258550163 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036276122309 : ℝ) / (1.295212 * 12378) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036276122310 : ℝ) / (1.29521 * 12378) := by gcongr
      _ ≤ (0.000258550163 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12378 BstLean.Part154.csC) ≤ 0.001034267501 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12378 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12378 BstLean.Part154.csC) (piBar (rhoBar 12378 BstLean.Part154.csC)) ≤ 0.000197482602 ∧
    cc1 (rhoBar 12378 BstLean.Part154.csC) (piBar (rhoBar 12378 BstLean.Part154.csC)) ≤ 0.000125659441 ∧
    cc2 (rhoBar 12378 BstLean.Part154.csC) ≤ 0.000072946207 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12378 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12378 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12378 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12378 BstLean.Part154.csC * nuR (rhoBar 12378 BstLean.Part154.csC)) ≤ 0.000517117038 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258550163 : ℝ) * 0.001034267501 := by gcongr
      _ ≤ (0.000517117038 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12378 BstLean.Part154.csC) * nuR (rhoBar 12378 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001034267501 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12378 BstLean.Part154.csC) * rhoBar 12378 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258550163 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258550163 / 2 + 0.399 * 0.001034267501 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197482602 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517117038 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125659441 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258550163 / 1.414213562 := by gcongr
      _ ≤ (0.000072946207 : ℝ) := by norm_num

end BstLean.Part269.N12378

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12378
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12378 BstLean.Part154.csC) (piBar (rhoBar 12378 BstLean.Part154.csC)) ≤ 1.68420E-7 := by
  have hr0 : 0 ≤ rhoBar 12378 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12378 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12378 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12378 BstLean.Part154.csC) (piBar (rhoBar 12378 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12378 BstLean.Part154.csC) (piBar (rhoBar 12378 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12378 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197482602 : ℝ) ^ 2 + 0.000125659441 ^ 2 + 3 * 0.000072946207 ^ 2 +
        2 * 0.797885 * 0.000197482602 * 0.000125659441 + 2 * 0.000197482602 * 0.000072946207 +
        4 * 0.797885 * 0.000125659441 * 0.000072946207 := by gcongr
    _ ≤ (1.68420E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12378 BstLean.Part154.csC Θ ≤ 0.002700132037 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12378 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12378 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12378 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12378 BstLean.Part154.csC) (piBar (rhoBar 12378 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12378 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036276122310 * 1.68420E-7 / (0.000258549763 : ℝ) := by gcongr
    _ ≤ 0.002700132037 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12378 BstLean.Part154.csC Θ ≤ 0.002997283838 + 0.000682276656 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12378 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12378 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12378 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036276122310 : ℝ) * ((2 * Θ * 0.000258550163 +
        (6863 / 10000) * 0.000258550163 * 12378 * 0.001034267501) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002997283838 + 0.000682276656 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12378 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12378 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12378 0.011 Θ ∧ gammaRatio 12378 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12378 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036276122310 : ℝ) * 0.525 / ((1 - 0.011) * 12378) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12378 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12378 0.011 Θ) :=
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
    badAllowance 12378 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12378 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12378 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12378 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12378 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12378 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12378 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12378 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12378 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12378 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12378 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036276122310 : ℝ) * 12378 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12378 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004097283838 + 0.003382408693 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12378

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12378
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12378 BstLean.Part154.csC) (piBar (rhoBar 12378 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12378 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12378 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12378 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12378 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12378 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12378 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12378 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12378 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12378 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12378 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12378 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12378 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12378 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12378 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053170040605 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12378) ≤ 0.010734096482 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12378 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036276122310)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010734096482 + 2 * 0.737676 / 12378) := by gcongr
    _ ≤ (0.053170040605 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12378 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12378

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12378
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488627686 : ℝ) ≤ plow 12378 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12378) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053379648402)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417569320) : eMP 12378 0.011 xi bn ≤ 0.001219994231 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12378 : ℝ) * (1 - 0.011))) ≤ 0.000603147773 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001417569320 / (12378 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603147773 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603147773 : ℝ) + 3.141593 * 0.053379648402 / (12378 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001219994231 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053379648402)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417569320) : PiBarMP 12378 12 0.011 xi bn ≤ 0.163358304585 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12378 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037650621775 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.642857880660 : ℝ) ≤ √((12378 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.256460486571 : ℝ) ≤ √(12378 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12378) ≤ 0.125227858246 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037650621775 + 0.053379648402 * 1.772454 / (2 * (110.642857880660 : ℝ))) * (1 + 0.001219994231) +
        8 / (12378 * 111.256460486571) + 0.125227858246 := by gcongr
    _ ≤ (0.163358304585 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053379648402)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417569320) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284210401586) :
    parallelOracle 12378 0.011 xi bn cd ≤ 0.164378251671 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12378 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12378 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488627686 : ℝ) ≤ plow 12378 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.256460486571 : ℝ) ≤ √(12378 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284210401586 : ℝ) / (2 * 0.560488627686 * 111.256460486571)) * 0.163358304585 +
        0.284210401586 ^ 2 / (2 * 0.560488627686 * 111.256460486571) := by gcongr
    _ ≤ (0.164378251671 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053379648402) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417569320)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284210401586) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12378 12378 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488627686 : ℝ) ≤ plow 12378 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.256460486571 : ℝ) ≤ √(12378 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12378 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12378 Θ 1.22 ≤ 0.011919312319 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.256460486571 := by gcongr <;> linarith
      _ ≤ (0.011919312319 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12378 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12378 12378 0.011 ≤ 0.008591744880 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12378 12378 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12378 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12378 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12378 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12378 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164378251671 + 0.011919312319 + (0.008591744880 : ℝ) *
        (1 + 2 * (0.284210401586 + 0.011919312319) / (0.560488627686 * 111.256460486571))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12378]

end BstLean.Part269.N12378

/-! The original eight local profiles supply actual 12378 moment certificates. -/
namespace BstLean.Part269.N12378
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12378 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12378 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12378 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053379648402 ∧
    0 ≤ bN 12378 BstLean.Part154.csC (groupTheta g) ∧ bN 12378 BstLean.Part154.csC (groupTheta g) ≤ 0.001417569320 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12378 12378 0.011
      (momentAllowance 12378 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12378 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12378 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12378 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12378 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12378 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231040360981 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12378 0.011
      (momentAllowance 12378 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12378 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12378
/-! The actual computed-centre upper energy formula at 12378. -/
namespace BstLean.Part269.N12378
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12378

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12378
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12378)
open BstLean.Part268 (cell12378)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086492299433
  | 2 => 0.087454966937
  | 3 => 0.088418915689
  | 4 => 0.089386268601
  | 5 => 0.090359566893
  | 6 => 0.091341828667
  | 7 => 0.092336612356
  | 8 => 0.093348084980
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12378 12378 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12378 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12378

/-! Actual upper energy certificates on all 43 source endpoints at 12378. -/
namespace BstLean.Part269.N12378
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12378)
open BstLean.Part268 (cell12378)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12378 (gMinus 12378) (1 - (cell12378 i).lower) ≤ 1 ∧
    energyUpper 12378 (gMinus 12378) (BstLean.Part211.gPlus 12378)
      (finiteEnergy 12378 12378 0.011) (1 - (cell12378 i).lower) ≤
      (cell12378 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨10,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨11,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨12,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨13,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨14,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨15,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨16,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨17,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨18,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨19,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨20,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨21,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨22,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨23,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨24,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨25,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨26,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨27,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨28,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨29,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨30,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨31,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨32,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨33,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨34,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨35,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨36,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨37,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨38,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨39,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨40,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨41,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨42,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨43,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨44,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨45,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨46,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨47,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨48,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨49,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨50,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨51,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12378) (by norm_num)
        (q := 1 - (cell12378 ⟨52,by decide⟩).lower)
        (by norm_num [cell12378]) (by norm_num [cell12378])
      exact ⟨E.1,E.2.trans (by norm_num [cell12378])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12378

/-! Source-cell containment and simple scalar guards at 12378. -/
namespace BstLean.Part269.N12378
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12378)
open BstLean.Part268 (cell12378)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12378 ⟨10,by decide⟩).lower ∧ (cell12378 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12378 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12378 ⟨11,by decide⟩).lower ∧ (cell12378 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12378 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12378 ⟨12,by decide⟩).lower ∧ (cell12378 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12378 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12378 ⟨13,by decide⟩).lower ∧ (cell12378 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12378 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12378 ⟨14,by decide⟩).lower ∧ (cell12378 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12378 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12378 ⟨15,by decide⟩).lower ∧ (cell12378 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12378 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12378 ⟨16,by decide⟩).lower ∧ (cell12378 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12378 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12378 ⟨17,by decide⟩).lower ∧ (cell12378 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12378 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12378 ⟨18,by decide⟩).lower ∧ (cell12378 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12378 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12378 ⟨19,by decide⟩).lower ∧ (cell12378 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12378 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12378 ⟨20,by decide⟩).lower ∧ (cell12378 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12378 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12378 ⟨21,by decide⟩).lower ∧ (cell12378 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12378 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12378 ⟨22,by decide⟩).lower ∧ (cell12378 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12378 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12378 ⟨23,by decide⟩).lower ∧ (cell12378 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12378 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12378 ⟨24,by decide⟩).lower ∧ (cell12378 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12378 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12378 ⟨25,by decide⟩).lower ∧ (cell12378 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12378 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12378 ⟨26,by decide⟩).lower ∧ (cell12378 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12378 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12378 ⟨27,by decide⟩).lower ∧ (cell12378 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12378 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12378 ⟨28,by decide⟩).lower ∧ (cell12378 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12378 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12378 ⟨29,by decide⟩).lower ∧ (cell12378 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12378 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12378 ⟨30,by decide⟩).lower ∧ (cell12378 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12378 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12378 ⟨31,by decide⟩).lower ∧ (cell12378 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12378 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12378 ⟨32,by decide⟩).lower ∧ (cell12378 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12378 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12378 ⟨33,by decide⟩).lower ∧ (cell12378 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12378 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12378 ⟨34,by decide⟩).lower ∧ (cell12378 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12378 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12378 ⟨35,by decide⟩).lower ∧ (cell12378 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12378 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12378 ⟨36,by decide⟩).lower ∧ (cell12378 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12378 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12378 ⟨37,by decide⟩).lower ∧ (cell12378 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12378 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12378 ⟨38,by decide⟩).lower ∧ (cell12378 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12378 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12378 ⟨39,by decide⟩).lower ∧ (cell12378 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12378 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12378 ⟨40,by decide⟩).lower ∧ (cell12378 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12378 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12378 ⟨41,by decide⟩).lower ∧ (cell12378 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12378 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12378 ⟨42,by decide⟩).lower ∧ (cell12378 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12378 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12378 ⟨43,by decide⟩).lower ∧ (cell12378 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12378 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12378 ⟨44,by decide⟩).lower ∧ (cell12378 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12378 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12378 ⟨45,by decide⟩).lower ∧ (cell12378 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12378 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12378 ⟨46,by decide⟩).lower ∧ (cell12378 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12378 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12378 ⟨47,by decide⟩).lower ∧ (cell12378 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12378 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12378 ⟨48,by decide⟩).lower ∧ (cell12378 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12378 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12378 ⟨49,by decide⟩).lower ∧ (cell12378 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12378 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12378 ⟨50,by decide⟩).lower ∧ (cell12378 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12378 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12378 ⟨51,by decide⟩).lower ∧ (cell12378 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12378 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12378 ⟨52,by decide⟩).lower ∧ (cell12378 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12378 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12378 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12378 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12378,cell12378,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12378 i).lower ∧
    (cell12378 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12378 i).upper ≤ (0.532 : ℝ) ∧
    (cell12378 i).centre ≤ (0.1 : ℝ) ∧ (cell12378 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12378 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12378 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12378

/-! The local source numeric instances at 12378 have no network premises. -/
namespace BstLean.Part269.N12378
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12378)
open BstLean.Part268 (cell12378)

noncomputable def sourceNumerics12378 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12378 (cell12378 i)
      scalarRow12378.M scalarRow12378.H scalarRow12378.xi := by
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
    energy_allowance := scalarRow12378.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12378]
    centre_nonneg := (scalarRow12378.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12378])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12378
/-! Actual 12379 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12379
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12379 ≤ (1.036274644000 : ℝ) := by
  have hr : (111.260954516847 : ℝ) ≤ √(12379 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.260954516847 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12379 12379 (11 / 1000) ≤
    (0.008591397841 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12379) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.260954516847 : ℝ) ≤ √(12379 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12379)
  have hdiv : K / √(12379 : ℝ) ≤ K / 111.260954516847 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.260954516847 ≤ (0.008591397841 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12379.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12379 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12379 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12379 := gPlus_lower 12379
end BstLean.Part269.N12379

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12379
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036274643999 : ℝ) ≤ wn 12379 := by
  have hn : √(12379 : ℝ) ≤ 111.260954516848 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12379 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.260954516848 ≤ 2 / √(12379 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258528508 : ℝ) ≤ rhoBar 12379 BstLean.Part154.csC ∧
    rhoBar 12379 BstLean.Part154.csC ≤ 0.000258528908 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036274643999 : ℝ) / (1.295212 * 12379) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036274644000 : ℝ) / (1.29521 * 12379) := by gcongr
      _ ≤ (0.000258528908 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12379 BstLean.Part154.csC) ≤ 0.001034182470 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12379 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12379 BstLean.Part154.csC) (piBar (rhoBar 12379 BstLean.Part154.csC)) ≤ 0.000197466366 ∧
    cc1 (rhoBar 12379 BstLean.Part154.csC) (piBar (rhoBar 12379 BstLean.Part154.csC)) ≤ 0.000125649110 ∧
    cc2 (rhoBar 12379 BstLean.Part154.csC) ≤ 0.000072940211 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12379 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12379 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12379 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12379 BstLean.Part154.csC * nuR (rhoBar 12379 BstLean.Part154.csC)) ≤ 0.000517074526 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258528908 : ℝ) * 0.001034182470 := by gcongr
      _ ≤ (0.000517074526 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12379 BstLean.Part154.csC) * nuR (rhoBar 12379 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001034182470 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12379 BstLean.Part154.csC) * rhoBar 12379 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258528908 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258528908 / 2 + 0.399 * 0.001034182470 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197466366 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517074526 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125649110 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258528908 / 1.414213562 := by gcongr
      _ ≤ (0.000072940211 : ℝ) := by norm_num

end BstLean.Part269.N12379

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12379
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12379 BstLean.Part154.csC) (piBar (rhoBar 12379 BstLean.Part154.csC)) ≤ 1.68392E-7 := by
  have hr0 : 0 ≤ rhoBar 12379 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12379 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12379 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12379 BstLean.Part154.csC) (piBar (rhoBar 12379 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12379 BstLean.Part154.csC) (piBar (rhoBar 12379 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12379 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197466366 : ℝ) ^ 2 + 0.000125649110 ^ 2 + 3 * 0.000072940211 ^ 2 +
        2 * 0.797885 * 0.000197466366 * 0.000125649110 + 2 * 0.000197466366 * 0.000072940211 +
        4 * 0.797885 * 0.000125649110 * 0.000072940211 := by gcongr
    _ ≤ (1.68392E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12379 BstLean.Part154.csC Θ ≤ 0.002699901241 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12379 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12379 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12379 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12379 BstLean.Part154.csC) (piBar (rhoBar 12379 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12379 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036274644000 * 1.68392E-7 / (0.000258528508 : ℝ) := by gcongr
    _ ≤ 0.002699901241 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12379 BstLean.Part154.csC Θ ≤ 0.002997028870 + 0.000682219594 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12379 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12379 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12379 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036274644000 : ℝ) * ((2 * Θ * 0.000258528908 +
        (6863 / 10000) * 0.000258528908 * 12379 * 0.001034182470) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002997028870 + 0.000682219594 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12379 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12379 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12379 0.011 Θ ∧ gammaRatio 12379 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12379 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036274644000 : ℝ) * 0.525 / ((1 - 0.011) * 12379) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12379 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12379 0.011 Θ) :=
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
    badAllowance 12379 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12379 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12379 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12379 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12379 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12379 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12379 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12379 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12379 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12379 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12379 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036274644000 : ℝ) * 12379 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12379 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004097028870 + 0.003382120835 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12379

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12379
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12379 BstLean.Part154.csC) (piBar (rhoBar 12379 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12379 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12379 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12379 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12379 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12379 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12379 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12379 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12379 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12379 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12379 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12379 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12379 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12379 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12379 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053167869390 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12379) ≤ 0.010733662913 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12379 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036274644000)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010733662913 + 2 * 0.737676 / 12379) := by gcongr
    _ ≤ (0.053167869390 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12379 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12379

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12379
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488675288 : ℝ) ≤ plow 12379 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12379) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053379242309)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417448152) : eMP 12379 0.011 xi bn ≤ 0.001219892742 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12379 : ℝ) * (1 - 0.011))) ≤ 0.000603097634 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001417448152 / (12379 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603097634 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603097634 : ℝ) + 3.141593 * 0.053379242309 / (12379 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001219892742 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053379242309)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417448152) : PiBarMP 12379 12 0.011 xi bn ≤ 0.163351610183 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12379 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037649012630 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.647327125421 : ℝ) ≤ √((12379 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.260954516847 : ℝ) ≤ √(12379 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12379) ≤ 0.125222800068 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037649012630 + 0.053379242309 * 1.772454 / (2 * (110.647327125421 : ℝ))) * (1 + 0.001219892742) +
        8 / (12379 * 111.260954516847) + 0.125222800068 := by gcongr
    _ ≤ (0.163351610183 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053379242309)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417448152) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284207351534) :
    parallelOracle 12379 0.011 xi bn cd ≤ 0.164371482835 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12379 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12379 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488675288 : ℝ) ≤ plow 12379 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.260954516847 : ℝ) ≤ √(12379 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284207351534 : ℝ) / (2 * 0.560488675288 * 111.260954516847)) * 0.163351610183 +
        0.284207351534 ^ 2 / (2 * 0.560488675288 * 111.260954516847) := by gcongr
    _ ≤ (0.164371482835 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053379242309) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417448152)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284207351534) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12379 12379 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488675288 : ℝ) ≤ plow 12379 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.260954516847 : ℝ) ≤ √(12379 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12379 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12379 Θ 1.22 ≤ 0.011918830877 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.260954516847 := by gcongr <;> linarith
      _ ≤ (0.011918830877 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12379 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12379 12379 0.011 ≤ 0.008591397841 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12379 12379 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12379 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12379 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12379 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12379 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164371482835 + 0.011918830877 + (0.008591397841 : ℝ) *
        (1 + 2 * (0.284207351534 + 0.011918830877) / (0.560488675288 * 111.260954516847))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12379]

end BstLean.Part269.N12379

/-! The original eight local profiles supply actual 12379 moment certificates. -/
namespace BstLean.Part269.N12379
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12379 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12379 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12379 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053379242309 ∧
    0 ≤ bN 12379 BstLean.Part154.csC (groupTheta g) ∧ bN 12379 BstLean.Part154.csC (groupTheta g) ≤ 0.001417448152 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12379 12379 0.011
      (momentAllowance 12379 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12379 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12379 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12379 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12379 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12379 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231039482144 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12379 0.011
      (momentAllowance 12379 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12379 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12379
/-! The actual computed-centre upper energy formula at 12379. -/
namespace BstLean.Part269.N12379
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12379

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12379
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12379)
open BstLean.Part268 (cell12379)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086488969141
  | 2 => 0.087451565296
  | 3 => 0.088415430724
  | 4 => 0.089382685713
  | 5 => 0.090355868416
  | 6 => 0.091337993378
  | 7 => 0.092332614928
  | 8 => 0.093343895389
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12379 12379 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12379 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12379

/-! Actual upper energy certificates on all 43 source endpoints at 12379. -/
namespace BstLean.Part269.N12379
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12379)
open BstLean.Part268 (cell12379)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12379 (gMinus 12379) (1 - (cell12379 i).lower) ≤ 1 ∧
    energyUpper 12379 (gMinus 12379) (BstLean.Part211.gPlus 12379)
      (finiteEnergy 12379 12379 0.011) (1 - (cell12379 i).lower) ≤
      (cell12379 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨10,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨11,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨12,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨13,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨14,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨15,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨16,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨17,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨18,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨19,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨20,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨21,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨22,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨23,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨24,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨25,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨26,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨27,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨28,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨29,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨30,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨31,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨32,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨33,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨34,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨35,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨36,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨37,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨38,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨39,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨40,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨41,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨42,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨43,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨44,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨45,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨46,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨47,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨48,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨49,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨50,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨51,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12379) (by norm_num)
        (q := 1 - (cell12379 ⟨52,by decide⟩).lower)
        (by norm_num [cell12379]) (by norm_num [cell12379])
      exact ⟨E.1,E.2.trans (by norm_num [cell12379])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12379

/-! Source-cell containment and simple scalar guards at 12379. -/
namespace BstLean.Part269.N12379
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12379)
open BstLean.Part268 (cell12379)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12379 ⟨10,by decide⟩).lower ∧ (cell12379 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12379 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12379 ⟨11,by decide⟩).lower ∧ (cell12379 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12379 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12379 ⟨12,by decide⟩).lower ∧ (cell12379 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12379 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12379 ⟨13,by decide⟩).lower ∧ (cell12379 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12379 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12379 ⟨14,by decide⟩).lower ∧ (cell12379 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12379 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12379 ⟨15,by decide⟩).lower ∧ (cell12379 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12379 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12379 ⟨16,by decide⟩).lower ∧ (cell12379 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12379 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12379 ⟨17,by decide⟩).lower ∧ (cell12379 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12379 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12379 ⟨18,by decide⟩).lower ∧ (cell12379 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12379 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12379 ⟨19,by decide⟩).lower ∧ (cell12379 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12379 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12379 ⟨20,by decide⟩).lower ∧ (cell12379 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12379 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12379 ⟨21,by decide⟩).lower ∧ (cell12379 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12379 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12379 ⟨22,by decide⟩).lower ∧ (cell12379 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12379 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12379 ⟨23,by decide⟩).lower ∧ (cell12379 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12379 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12379 ⟨24,by decide⟩).lower ∧ (cell12379 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12379 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12379 ⟨25,by decide⟩).lower ∧ (cell12379 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12379 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12379 ⟨26,by decide⟩).lower ∧ (cell12379 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12379 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12379 ⟨27,by decide⟩).lower ∧ (cell12379 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12379 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12379 ⟨28,by decide⟩).lower ∧ (cell12379 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12379 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12379 ⟨29,by decide⟩).lower ∧ (cell12379 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12379 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12379 ⟨30,by decide⟩).lower ∧ (cell12379 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12379 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12379 ⟨31,by decide⟩).lower ∧ (cell12379 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12379 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12379 ⟨32,by decide⟩).lower ∧ (cell12379 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12379 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12379 ⟨33,by decide⟩).lower ∧ (cell12379 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12379 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12379 ⟨34,by decide⟩).lower ∧ (cell12379 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12379 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12379 ⟨35,by decide⟩).lower ∧ (cell12379 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12379 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12379 ⟨36,by decide⟩).lower ∧ (cell12379 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12379 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12379 ⟨37,by decide⟩).lower ∧ (cell12379 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12379 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12379 ⟨38,by decide⟩).lower ∧ (cell12379 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12379 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12379 ⟨39,by decide⟩).lower ∧ (cell12379 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12379 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12379 ⟨40,by decide⟩).lower ∧ (cell12379 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12379 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12379 ⟨41,by decide⟩).lower ∧ (cell12379 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12379 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12379 ⟨42,by decide⟩).lower ∧ (cell12379 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12379 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12379 ⟨43,by decide⟩).lower ∧ (cell12379 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12379 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12379 ⟨44,by decide⟩).lower ∧ (cell12379 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12379 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12379 ⟨45,by decide⟩).lower ∧ (cell12379 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12379 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12379 ⟨46,by decide⟩).lower ∧ (cell12379 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12379 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12379 ⟨47,by decide⟩).lower ∧ (cell12379 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12379 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12379 ⟨48,by decide⟩).lower ∧ (cell12379 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12379 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12379 ⟨49,by decide⟩).lower ∧ (cell12379 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12379 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12379 ⟨50,by decide⟩).lower ∧ (cell12379 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12379 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12379 ⟨51,by decide⟩).lower ∧ (cell12379 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12379 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12379 ⟨52,by decide⟩).lower ∧ (cell12379 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12379 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12379 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12379 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12379,cell12379,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12379 i).lower ∧
    (cell12379 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12379 i).upper ≤ (0.532 : ℝ) ∧
    (cell12379 i).centre ≤ (0.1 : ℝ) ∧ (cell12379 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12379 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12379 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12379

/-! The local source numeric instances at 12379 have no network premises. -/
namespace BstLean.Part269.N12379
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12379)
open BstLean.Part268 (cell12379)

noncomputable def sourceNumerics12379 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12379 (cell12379 i)
      scalarRow12379.M scalarRow12379.H scalarRow12379.xi := by
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
    energy_allowance := scalarRow12379.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12379]
    centre_nonneg := (scalarRow12379.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12379])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12379
/-! Actual 12380 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12380
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12380 ≤ (1.036273165870 : ℝ) := by
  have hr : (111.265448365608 : ℝ) ≤ √(12380 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.265448365608 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12380 12380 (11 / 1000) ≤
    (0.008591050844 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12380) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.265448365608 : ℝ) ≤ √(12380 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12380)
  have hdiv : K / √(12380 : ℝ) ≤ K / 111.265448365608 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.265448365608 ≤ (0.008591050844 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12380.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12380 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12380 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12380 := gPlus_lower 12380
end BstLean.Part269.N12380

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12380
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036273165869 : ℝ) ≤ wn 12380 := by
  have hn : √(12380 : ℝ) ≤ 111.265448365609 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12380 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.265448365609 ≤ 2 / √(12380 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258507257 : ℝ) ≤ rhoBar 12380 BstLean.Part154.csC ∧
    rhoBar 12380 BstLean.Part154.csC ≤ 0.000258507657 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036273165869 : ℝ) / (1.295212 * 12380) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036273165870 : ℝ) / (1.29521 * 12380) := by gcongr
      _ ≤ (0.000258507657 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12380 BstLean.Part154.csC) ≤ 0.001034097455 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12380 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12380 BstLean.Part154.csC) (piBar (rhoBar 12380 BstLean.Part154.csC)) ≤ 0.000197450134 ∧
    cc1 (rhoBar 12380 BstLean.Part154.csC) (piBar (rhoBar 12380 BstLean.Part154.csC)) ≤ 0.000125638782 ∧
    cc2 (rhoBar 12380 BstLean.Part154.csC) ≤ 0.000072934215 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12380 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12380 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12380 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12380 BstLean.Part154.csC * nuR (rhoBar 12380 BstLean.Part154.csC)) ≤ 0.000517032021 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258507657 : ℝ) * 0.001034097455 := by gcongr
      _ ≤ (0.000517032021 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12380 BstLean.Part154.csC) * nuR (rhoBar 12380 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001034097455 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12380 BstLean.Part154.csC) * rhoBar 12380 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258507657 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258507657 / 2 + 0.399 * 0.001034097455 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197450134 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000517032021 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125638782 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258507657 / 1.414213562 := by gcongr
      _ ≤ (0.000072934215 : ℝ) := by norm_num

end BstLean.Part269.N12380

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12380
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12380 BstLean.Part154.csC) (piBar (rhoBar 12380 BstLean.Part154.csC)) ≤ 1.68364E-7 := by
  have hr0 : 0 ≤ rhoBar 12380 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12380 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12380 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12380 BstLean.Part154.csC) (piBar (rhoBar 12380 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12380 BstLean.Part154.csC) (piBar (rhoBar 12380 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12380 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197450134 : ℝ) ^ 2 + 0.000125638782 ^ 2 + 3 * 0.000072934215 ^ 2 +
        2 * 0.797885 * 0.000197450134 * 0.000125638782 + 2 * 0.000197450134 * 0.000072934215 +
        4 * 0.797885 * 0.000125638782 * 0.000072934215 := by gcongr
    _ ≤ (1.68364E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12380 BstLean.Part154.csC Θ ≤ 0.002699670367 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12380 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12380 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12380 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12380 BstLean.Part154.csC) (piBar (rhoBar 12380 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12380 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036273165870 * 1.68364E-7 / (0.000258507257 : ℝ) := by gcongr
    _ ≤ 0.002699670367 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12380 BstLean.Part154.csC Θ ≤ 0.002996773956 + 0.000682162543 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12380 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12380 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12380 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036273165870 : ℝ) * ((2 * Θ * 0.000258507657 +
        (6863 / 10000) * 0.000258507657 * 12380 * 0.001034097455) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002996773956 + 0.000682162543 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12380 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12380 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12380 0.011 Θ ∧ gammaRatio 12380 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12380 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036273165870 : ℝ) * 0.525 / ((1 - 0.011) * 12380) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12380 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12380 0.011 Θ) :=
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
    badAllowance 12380 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12380 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12380 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12380 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12380 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12380 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12380 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12380 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12380 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12380 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12380 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036273165870 : ℝ) * 12380 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12380 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004096773956 + 0.003381832910 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12380

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12380
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12380 BstLean.Part154.csC) (piBar (rhoBar 12380 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12380 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12380 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12380 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12380 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12380 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12380 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12380 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12380 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12380 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12380 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12380 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12380 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12380 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12380 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053165698436 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12380) ≤ 0.010733229396 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12380 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036273165870)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010733229396 + 2 * 0.737676 / 12380) := by gcongr
    _ ≤ (0.053165698436 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12380 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12380

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12380
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488722883 : ℝ) ≤ plow 12380 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12380) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053378836234)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417326943) : eMP 12380 0.011 xi bn ≤ 0.001219791243 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12380 : ℝ) * (1 - 0.011))) ≤ 0.000603047490 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001417326943 / (12380 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000603047490 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000603047490 : ℝ) + 3.141593 * 0.053378836234 / (12380 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001219791243 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053378836234)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417326943) : PiBarMP 12380 12 0.011 xi bn ≤ 0.163344915782 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12380 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037647402872 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.651796189668 : ℝ) ≤ √((12380 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.265448365608 : ℝ) ≤ √(12380 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12380) ≤ 0.125217742502 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037647402872 + 0.053378836234 * 1.772454 / (2 * (110.651796189668 : ℝ))) * (1 + 0.001219791243) +
        8 / (12380 * 111.265448365608) + 0.125217742502 := by gcongr
    _ ≤ (0.163344915782 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053378836234)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417326943) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284204301778) :
    parallelOracle 12380 0.011 xi bn cd ≤ 0.164364714009 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12380 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12380 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488722883 : ℝ) ≤ plow 12380 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.265448365608 : ℝ) ≤ √(12380 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284204301778 : ℝ) / (2 * 0.560488722883 * 111.265448365608)) * 0.163344915782 +
        0.284204301778 ^ 2 / (2 * 0.560488722883 * 111.265448365608) := by gcongr
    _ ≤ (0.164364714009 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053378836234) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417326943)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284204301778) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12380 12380 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488722883 : ℝ) ≤ plow 12380 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.265448365608 : ℝ) ≤ √(12380 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12380 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12380 Θ 1.22 ≤ 0.011918349492 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.265448365608 := by gcongr <;> linarith
      _ ≤ (0.011918349492 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12380 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12380 12380 0.011 ≤ 0.008591050844 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12380 12380 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12380 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12380 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12380 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12380 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164364714009 + 0.011918349492 + (0.008591050844 : ℝ) *
        (1 + 2 * (0.284204301778 + 0.011918349492) / (0.560488722883 * 111.265448365608))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12380]

end BstLean.Part269.N12380

/-! The original eight local profiles supply actual 12380 moment certificates. -/
namespace BstLean.Part269.N12380
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12380 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12380 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12380 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053378836234 ∧
    0 ≤ bN 12380 BstLean.Part154.csC (groupTheta g) ∧ bN 12380 BstLean.Part154.csC (groupTheta g) ≤ 0.001417326943 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12380 12380 0.011
      (momentAllowance 12380 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12380 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12380 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12380 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12380 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12380 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231038603342 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12380 0.011
      (momentAllowance 12380 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12380 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12380
/-! The actual computed-centre upper energy formula at 12380. -/
namespace BstLean.Part269.N12380
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12380

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12380
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12380)
open BstLean.Part268 (cell12380)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086485640371
  | 2 => 0.087448165244
  | 3 => 0.088411947432
  | 4 => 0.089379104600
  | 5 => 0.090352171839
  | 6 => 0.091334160138
  | 7 => 0.092328619731
  | 8 => 0.093339708247
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12380 12380 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12380 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12380

/-! Actual upper energy certificates on all 43 source endpoints at 12380. -/
namespace BstLean.Part269.N12380
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12380)
open BstLean.Part268 (cell12380)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12380 (gMinus 12380) (1 - (cell12380 i).lower) ≤ 1 ∧
    energyUpper 12380 (gMinus 12380) (BstLean.Part211.gPlus 12380)
      (finiteEnergy 12380 12380 0.011) (1 - (cell12380 i).lower) ≤
      (cell12380 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨10,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨11,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨12,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨13,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨14,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨15,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨16,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨17,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨18,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨19,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨20,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨21,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨22,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨23,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨24,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨25,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨26,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨27,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨28,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨29,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨30,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨31,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨32,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨33,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨34,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨35,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨36,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨37,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨38,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨39,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨40,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨41,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨42,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨43,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨44,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨45,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨46,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨47,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨48,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨49,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨50,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨51,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12380) (by norm_num)
        (q := 1 - (cell12380 ⟨52,by decide⟩).lower)
        (by norm_num [cell12380]) (by norm_num [cell12380])
      exact ⟨E.1,E.2.trans (by norm_num [cell12380])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12380

/-! Source-cell containment and simple scalar guards at 12380. -/
namespace BstLean.Part269.N12380
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12380)
open BstLean.Part268 (cell12380)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12380 ⟨10,by decide⟩).lower ∧ (cell12380 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12380 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12380 ⟨11,by decide⟩).lower ∧ (cell12380 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12380 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12380 ⟨12,by decide⟩).lower ∧ (cell12380 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12380 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12380 ⟨13,by decide⟩).lower ∧ (cell12380 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12380 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12380 ⟨14,by decide⟩).lower ∧ (cell12380 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12380 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12380 ⟨15,by decide⟩).lower ∧ (cell12380 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12380 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12380 ⟨16,by decide⟩).lower ∧ (cell12380 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12380 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12380 ⟨17,by decide⟩).lower ∧ (cell12380 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12380 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12380 ⟨18,by decide⟩).lower ∧ (cell12380 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12380 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12380 ⟨19,by decide⟩).lower ∧ (cell12380 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12380 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12380 ⟨20,by decide⟩).lower ∧ (cell12380 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12380 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12380 ⟨21,by decide⟩).lower ∧ (cell12380 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12380 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12380 ⟨22,by decide⟩).lower ∧ (cell12380 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12380 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12380 ⟨23,by decide⟩).lower ∧ (cell12380 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12380 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12380 ⟨24,by decide⟩).lower ∧ (cell12380 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12380 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12380 ⟨25,by decide⟩).lower ∧ (cell12380 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12380 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12380 ⟨26,by decide⟩).lower ∧ (cell12380 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12380 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12380 ⟨27,by decide⟩).lower ∧ (cell12380 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12380 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12380 ⟨28,by decide⟩).lower ∧ (cell12380 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12380 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12380 ⟨29,by decide⟩).lower ∧ (cell12380 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12380 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12380 ⟨30,by decide⟩).lower ∧ (cell12380 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12380 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12380 ⟨31,by decide⟩).lower ∧ (cell12380 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12380 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12380 ⟨32,by decide⟩).lower ∧ (cell12380 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12380 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12380 ⟨33,by decide⟩).lower ∧ (cell12380 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12380 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12380 ⟨34,by decide⟩).lower ∧ (cell12380 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12380 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12380 ⟨35,by decide⟩).lower ∧ (cell12380 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12380 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12380 ⟨36,by decide⟩).lower ∧ (cell12380 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12380 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12380 ⟨37,by decide⟩).lower ∧ (cell12380 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12380 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12380 ⟨38,by decide⟩).lower ∧ (cell12380 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12380 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12380 ⟨39,by decide⟩).lower ∧ (cell12380 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12380 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12380 ⟨40,by decide⟩).lower ∧ (cell12380 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12380 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12380 ⟨41,by decide⟩).lower ∧ (cell12380 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12380 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12380 ⟨42,by decide⟩).lower ∧ (cell12380 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12380 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12380 ⟨43,by decide⟩).lower ∧ (cell12380 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12380 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12380 ⟨44,by decide⟩).lower ∧ (cell12380 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12380 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12380 ⟨45,by decide⟩).lower ∧ (cell12380 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12380 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12380 ⟨46,by decide⟩).lower ∧ (cell12380 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12380 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12380 ⟨47,by decide⟩).lower ∧ (cell12380 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12380 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12380 ⟨48,by decide⟩).lower ∧ (cell12380 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12380 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12380 ⟨49,by decide⟩).lower ∧ (cell12380 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12380 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12380 ⟨50,by decide⟩).lower ∧ (cell12380 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12380 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12380 ⟨51,by decide⟩).lower ∧ (cell12380 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12380 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12380 ⟨52,by decide⟩).lower ∧ (cell12380 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12380 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12380 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12380 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12380,cell12380,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12380 i).lower ∧
    (cell12380 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12380 i).upper ≤ (0.532 : ℝ) ∧
    (cell12380 i).centre ≤ (0.1 : ℝ) ∧ (cell12380 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12380 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12380 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12380

/-! The local source numeric instances at 12380 have no network premises. -/
namespace BstLean.Part269.N12380
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12380)
open BstLean.Part268 (cell12380)

noncomputable def sourceNumerics12380 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12380 (cell12380 i)
      scalarRow12380.M scalarRow12380.H scalarRow12380.xi := by
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
    energy_allowance := scalarRow12380.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12380]
    centre_nonneg := (scalarRow12380.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12380])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12380
/-! Actual 12381 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12381
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12381 ≤ (1.036271687920 : ℝ) := by
  have hr : (111.269942032877 : ℝ) ≤ √(12381 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.269942032877 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12381 12381 (11 / 1000) ≤
    (0.008590703889 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12381) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.269942032877 : ℝ) ≤ √(12381 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12381)
  have hdiv : K / √(12381 : ℝ) ≤ K / 111.269942032877 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.269942032877 ≤ (0.008590703889 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12381.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12381 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12381 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12381 := gPlus_lower 12381
end BstLean.Part269.N12381

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12381
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036271687919 : ℝ) ≤ wn 12381 := by
  have hn : √(12381 : ℝ) ≤ 111.269942032878 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12381 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.269942032878 ≤ 2 / √(12381 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258486009 : ℝ) ≤ rhoBar 12381 BstLean.Part154.csC ∧
    rhoBar 12381 BstLean.Part154.csC ≤ 0.000258486409 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036271687919 : ℝ) / (1.295212 * 12381) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036271687920 : ℝ) / (1.29521 * 12381) := by gcongr
      _ ≤ (0.000258486409 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12381 BstLean.Part154.csC) ≤ 0.001034012452 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12381 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12381 BstLean.Part154.csC) (piBar (rhoBar 12381 BstLean.Part154.csC)) ≤ 0.000197433904 ∧
    cc1 (rhoBar 12381 BstLean.Part154.csC) (piBar (rhoBar 12381 BstLean.Part154.csC)) ≤ 0.000125628454 ∧
    cc2 (rhoBar 12381 BstLean.Part154.csC) ≤ 0.000072928220 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12381 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12381 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12381 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12381 BstLean.Part154.csC * nuR (rhoBar 12381 BstLean.Part154.csC)) ≤ 0.000516989522 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258486409 : ℝ) * 0.001034012452 := by gcongr
      _ ≤ (0.000516989522 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12381 BstLean.Part154.csC) * nuR (rhoBar 12381 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001034012452 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12381 BstLean.Part154.csC) * rhoBar 12381 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258486409 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258486409 / 2 + 0.399 * 0.001034012452 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197433904 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516989522 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125628454 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258486409 / 1.414213562 := by gcongr
      _ ≤ (0.000072928220 : ℝ) := by norm_num

end BstLean.Part269.N12381

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12381
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12381 BstLean.Part154.csC) (piBar (rhoBar 12381 BstLean.Part154.csC)) ≤ 1.68337E-7 := by
  have hr0 : 0 ≤ rhoBar 12381 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12381 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12381 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12381 BstLean.Part154.csC) (piBar (rhoBar 12381 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12381 BstLean.Part154.csC) (piBar (rhoBar 12381 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12381 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197433904 : ℝ) ^ 2 + 0.000125628454 ^ 2 + 3 * 0.000072928220 ^ 2 +
        2 * 0.797885 * 0.000197433904 * 0.000125628454 + 2 * 0.000197433904 * 0.000072928220 +
        4 * 0.797885 * 0.000125628454 * 0.000072928220 := by gcongr
    _ ≤ (1.68337E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12381 BstLean.Part154.csC Θ ≤ 0.002699455461 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12381 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12381 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12381 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12381 BstLean.Part154.csC) (piBar (rhoBar 12381 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12381 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036271687920 * 1.68337E-7 / (0.000258486009 : ℝ) := by gcongr
    _ ≤ 0.002699455461 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12381 BstLean.Part154.csC Θ ≤ 0.002996519073 + 0.000682105500 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12381 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12381 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12381 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036271687920 : ℝ) * ((2 * Θ * 0.000258486409 +
        (6863 / 10000) * 0.000258486409 * 12381 * 0.001034012452) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002996519073 + 0.000682105500 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12381 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12381 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12381 0.011 Θ ∧ gammaRatio 12381 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12381 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036271687920 : ℝ) * 0.525 / ((1 - 0.011) * 12381) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12381 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12381 0.011 Θ) :=
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
    badAllowance 12381 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12381 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12381 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12381 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12381 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12381 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12381 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12381 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12381 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12381 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12381 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036271687920 : ℝ) * 12381 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12381 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004096519073 + 0.003381560961 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12381

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12381
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12381 BstLean.Part154.csC) (piBar (rhoBar 12381 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12381 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12381 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12381 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12381 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12381 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12381 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12381 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12381 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12381 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12381 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12381 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12381 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12381 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12381 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053163527745 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12381) ≤ 0.010732795931 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12381 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036271687920)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010732795931 + 2 * 0.737676 / 12381) := by gcongr
    _ ≤ (0.053163527745 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12381 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12381

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12381
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488770470 : ℝ) ≤ plow 12381 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12381) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053378438578)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417214118) : eMP 12381 0.011 xi bn ≤ 0.001219693323 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12381 : ℝ) * (1 - 0.011))) ≤ 0.000602999134 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001417214118 / (12381 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602999134 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602999134 : ℝ) + 3.141593 * 0.053378438578 / (12381 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001219693323 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053378438578)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417214118) : PiBarMP 12381 12 0.011 xi bn ≤ 0.163338333622 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12381 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037645904399 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.656265073424 : ℝ) ≤ √((12381 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.269942032877 : ℝ) ≤ √(12381 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12381) ≤ 0.125212685549 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037645904399 + 0.053378438578 * 1.772454 / (2 * (110.656265073424 : ℝ))) * (1 + 0.001219693323) +
        8 / (12381 * 111.269942032877) + 0.125212685549 := by gcongr
    _ ≤ (0.163338333622 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053378438578)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417214118) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284201270502) :
    parallelOracle 12381 0.011 xi bn cd ≤ 0.164358057797 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12381 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12381 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488770470 : ℝ) ≤ plow 12381 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.269942032877 : ℝ) ≤ √(12381 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284201270502 : ℝ) / (2 * 0.560488770470 * 111.269942032877)) * 0.163338333622 +
        0.284201270502 ^ 2 / (2 * 0.560488770470 * 111.269942032877) := by gcongr
    _ ≤ (0.164358057797 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053378438578) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417214118)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284201270502) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12381 12381 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488770470 : ℝ) ≤ plow 12381 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.269942032877 : ℝ) ≤ √(12381 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12381 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12381 Θ 1.22 ≤ 0.011917868167 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.269942032877 := by gcongr <;> linarith
      _ ≤ (0.011917868167 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12381 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12381 12381 0.011 ≤ 0.008590703889 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12381 12381 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12381 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12381 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12381 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12381 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164358057797 + 0.011917868167 + (0.008590703889 : ℝ) *
        (1 + 2 * (0.284201270502 + 0.011917868167) / (0.560488770470 * 111.269942032877))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12381]

end BstLean.Part269.N12381

/-! The original eight local profiles supply actual 12381 moment certificates. -/
namespace BstLean.Part269.N12381
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12381 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12381 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12381 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053378438578 ∧
    0 ≤ bN 12381 BstLean.Part154.csC (groupTheta g) ∧ bN 12381 BstLean.Part154.csC (groupTheta g) ≤ 0.001417214118 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12381 12381 0.011
      (momentAllowance 12381 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12381 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12381 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12381 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12381 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12381 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231037742757 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12381 0.011
      (momentAllowance 12381 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12381 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12381
/-! The actual computed-centre upper energy formula at 12381. -/
namespace BstLean.Part269.N12381
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12381

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12381
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12381)
open BstLean.Part268 (cell12381)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086482313120
  | 2 => 0.087444766778
  | 3 => 0.088408465810
  | 4 => 0.089375525260
  | 5 => 0.090348477158
  | 6 => 0.091330328946
  | 7 => 0.092324626764
  | 8 => 0.093335523551
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12381 12381 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12381 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12381

/-! Actual upper energy certificates on all 43 source endpoints at 12381. -/
namespace BstLean.Part269.N12381
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12381)
open BstLean.Part268 (cell12381)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12381 (gMinus 12381) (1 - (cell12381 i).lower) ≤ 1 ∧
    energyUpper 12381 (gMinus 12381) (BstLean.Part211.gPlus 12381)
      (finiteEnergy 12381 12381 0.011) (1 - (cell12381 i).lower) ≤
      (cell12381 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨10,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨11,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨12,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨13,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨14,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨15,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨16,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨17,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨18,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨19,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨20,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨21,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨22,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨23,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨24,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨25,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨26,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨27,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨28,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨29,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨30,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨31,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨32,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨33,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨34,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨35,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨36,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨37,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨38,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨39,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨40,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨41,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨42,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨43,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨44,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨45,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨46,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨47,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨48,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨49,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨50,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨51,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12381) (by norm_num)
        (q := 1 - (cell12381 ⟨52,by decide⟩).lower)
        (by norm_num [cell12381]) (by norm_num [cell12381])
      exact ⟨E.1,E.2.trans (by norm_num [cell12381])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12381

/-! Source-cell containment and simple scalar guards at 12381. -/
namespace BstLean.Part269.N12381
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12381)
open BstLean.Part268 (cell12381)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12381 ⟨10,by decide⟩).lower ∧ (cell12381 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12381 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12381 ⟨11,by decide⟩).lower ∧ (cell12381 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12381 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12381 ⟨12,by decide⟩).lower ∧ (cell12381 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12381 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12381 ⟨13,by decide⟩).lower ∧ (cell12381 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12381 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12381 ⟨14,by decide⟩).lower ∧ (cell12381 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12381 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12381 ⟨15,by decide⟩).lower ∧ (cell12381 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12381 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12381 ⟨16,by decide⟩).lower ∧ (cell12381 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12381 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12381 ⟨17,by decide⟩).lower ∧ (cell12381 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12381 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12381 ⟨18,by decide⟩).lower ∧ (cell12381 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12381 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12381 ⟨19,by decide⟩).lower ∧ (cell12381 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12381 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12381 ⟨20,by decide⟩).lower ∧ (cell12381 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12381 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12381 ⟨21,by decide⟩).lower ∧ (cell12381 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12381 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12381 ⟨22,by decide⟩).lower ∧ (cell12381 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12381 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12381 ⟨23,by decide⟩).lower ∧ (cell12381 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12381 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12381 ⟨24,by decide⟩).lower ∧ (cell12381 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12381 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12381 ⟨25,by decide⟩).lower ∧ (cell12381 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12381 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12381 ⟨26,by decide⟩).lower ∧ (cell12381 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12381 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12381 ⟨27,by decide⟩).lower ∧ (cell12381 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12381 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12381 ⟨28,by decide⟩).lower ∧ (cell12381 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12381 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12381 ⟨29,by decide⟩).lower ∧ (cell12381 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12381 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12381 ⟨30,by decide⟩).lower ∧ (cell12381 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12381 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12381 ⟨31,by decide⟩).lower ∧ (cell12381 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12381 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12381 ⟨32,by decide⟩).lower ∧ (cell12381 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12381 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12381 ⟨33,by decide⟩).lower ∧ (cell12381 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12381 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12381 ⟨34,by decide⟩).lower ∧ (cell12381 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12381 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12381 ⟨35,by decide⟩).lower ∧ (cell12381 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12381 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12381 ⟨36,by decide⟩).lower ∧ (cell12381 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12381 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12381 ⟨37,by decide⟩).lower ∧ (cell12381 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12381 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12381 ⟨38,by decide⟩).lower ∧ (cell12381 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12381 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12381 ⟨39,by decide⟩).lower ∧ (cell12381 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12381 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12381 ⟨40,by decide⟩).lower ∧ (cell12381 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12381 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12381 ⟨41,by decide⟩).lower ∧ (cell12381 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12381 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12381 ⟨42,by decide⟩).lower ∧ (cell12381 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12381 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12381 ⟨43,by decide⟩).lower ∧ (cell12381 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12381 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12381 ⟨44,by decide⟩).lower ∧ (cell12381 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12381 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12381 ⟨45,by decide⟩).lower ∧ (cell12381 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12381 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12381 ⟨46,by decide⟩).lower ∧ (cell12381 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12381 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12381 ⟨47,by decide⟩).lower ∧ (cell12381 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12381 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12381 ⟨48,by decide⟩).lower ∧ (cell12381 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12381 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12381 ⟨49,by decide⟩).lower ∧ (cell12381 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12381 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12381 ⟨50,by decide⟩).lower ∧ (cell12381 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12381 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12381 ⟨51,by decide⟩).lower ∧ (cell12381 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12381 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12381 ⟨52,by decide⟩).lower ∧ (cell12381 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12381 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12381 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12381 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12381,cell12381,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12381 i).lower ∧
    (cell12381 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12381 i).upper ≤ (0.532 : ℝ) ∧
    (cell12381 i).centre ≤ (0.1 : ℝ) ∧ (cell12381 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12381 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12381 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12381

/-! The local source numeric instances at 12381 have no network premises. -/
namespace BstLean.Part269.N12381
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12381)
open BstLean.Part268 (cell12381)

noncomputable def sourceNumerics12381 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12381 (cell12381 i)
      scalarRow12381.M scalarRow12381.H scalarRow12381.xi := by
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
    energy_allowance := scalarRow12381.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12381]
    centre_nonneg := (scalarRow12381.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12381])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12381
/-! Actual 12382 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12382
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12382 ≤ (1.036270210150 : ℝ) := by
  have hr : (111.274435518676 : ℝ) ≤ √(12382 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.274435518676 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12382 12382 (11 / 1000) ≤
    (0.008590356977 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12382) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.274435518676 : ℝ) ≤ √(12382 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12382)
  have hdiv : K / √(12382 : ℝ) ≤ K / 111.274435518676 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.274435518676 ≤ (0.008590356977 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12382.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12382 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12382 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12382 := gPlus_lower 12382
end BstLean.Part269.N12382

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12382
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036270210149 : ℝ) ≤ wn 12382 := by
  have hn : √(12382 : ℝ) ≤ 111.274435518677 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12382 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.274435518677 ≤ 2 / √(12382 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258464764 : ℝ) ≤ rhoBar 12382 BstLean.Part154.csC ∧
    rhoBar 12382 BstLean.Part154.csC ≤ 0.000258465164 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036270210149 : ℝ) / (1.295212 * 12382) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036270210150 : ℝ) / (1.29521 * 12382) := by gcongr
      _ ≤ (0.000258465164 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12382 BstLean.Part154.csC) ≤ 0.001033927461 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12382 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12382 BstLean.Part154.csC) (piBar (rhoBar 12382 BstLean.Part154.csC)) ≤ 0.000197417676 ∧
    cc1 (rhoBar 12382 BstLean.Part154.csC) (piBar (rhoBar 12382 BstLean.Part154.csC)) ≤ 0.000125618129 ∧
    cc2 (rhoBar 12382 BstLean.Part154.csC) ≤ 0.000072922226 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12382 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12382 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12382 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12382 BstLean.Part154.csC * nuR (rhoBar 12382 BstLean.Part154.csC)) ≤ 0.000516947029 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258465164 : ℝ) * 0.001033927461 := by gcongr
      _ ≤ (0.000516947029 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12382 BstLean.Part154.csC) * nuR (rhoBar 12382 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001033927461 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12382 BstLean.Part154.csC) * rhoBar 12382 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258465164 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258465164 / 2 + 0.399 * 0.001033927461 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197417676 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516947029 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125618129 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258465164 / 1.414213562 := by gcongr
      _ ≤ (0.000072922226 : ℝ) := by norm_num

end BstLean.Part269.N12382

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12382
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12382 BstLean.Part154.csC) (piBar (rhoBar 12382 BstLean.Part154.csC)) ≤ 1.68309E-7 := by
  have hr0 : 0 ≤ rhoBar 12382 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12382 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12382 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12382 BstLean.Part154.csC) (piBar (rhoBar 12382 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12382 BstLean.Part154.csC) (piBar (rhoBar 12382 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12382 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197417676 : ℝ) ^ 2 + 0.000125618129 ^ 2 + 3 * 0.000072922226 ^ 2 +
        2 * 0.797885 * 0.000197417676 * 0.000125618129 + 2 * 0.000197417676 * 0.000072922226 +
        4 * 0.797885 * 0.000125618129 * 0.000072922226 := by gcongr
    _ ≤ (1.68309E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12382 BstLean.Part154.csC Θ ≤ 0.002699224453 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12382 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12382 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12382 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12382 BstLean.Part154.csC) (piBar (rhoBar 12382 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12382 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036270210150 * 1.68309E-7 / (0.000258464764 : ℝ) := by gcongr
    _ ≤ 0.002699224453 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12382 BstLean.Part154.csC Θ ≤ 0.002996264223 + 0.000682048465 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12382 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12382 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12382 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036270210150 : ℝ) * ((2 * Θ * 0.000258465164 +
        (6863 / 10000) * 0.000258465164 * 12382 * 0.001033927461) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002996264223 + 0.000682048465 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12382 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12382 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12382 0.011 Θ ∧ gammaRatio 12382 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12382 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036270210150 : ℝ) * 0.525 / ((1 - 0.011) * 12382) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12382 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12382 0.011 Θ) :=
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
    badAllowance 12382 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12382 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12382 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12382 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12382 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12382 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12382 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12382 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12382 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12382 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12382 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036270210150 : ℝ) * 12382 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12382 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004096264223 + 0.003381272918 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12382

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12382
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12382 BstLean.Part154.csC) (piBar (rhoBar 12382 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12382 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12382 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12382 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12382 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12382 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12382 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12382 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12382 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12382 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12382 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12382 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12382 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12382 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12382 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053161357321 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12382) ≤ 0.010732362519 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12382 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036270210150)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010732362519 + 2 * 0.737676 / 12382) := by gcongr
    _ ≤ (0.053161357321 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12382 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12382

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12382
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488818050 : ℝ) ≤ plow 12382 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12382) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053378032505)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417092838) : eMP 12382 0.011 xi bn ≤ 0.001219591809 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12382 : ℝ) * (1 - 0.011))) ≤ 0.000602948982 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001417092838 / (12382 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602948982 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602948982 : ℝ) + 3.141593 * 0.053378032505 / (12382 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001219591809 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053378032505)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417092838) : PiBarMP 12382 12 0.011 xi bn ≤ 0.163331639374 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12382 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037644293565 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.660733776710 : ℝ) ≤ √((12382 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.274435518676 : ℝ) ≤ √(12382 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12382) ≤ 0.125207629209 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037644293565 + 0.053378032505 * 1.772454 / (2 * (110.660733776710 : ℝ))) * (1 + 0.001219591809) +
        8 / (12382 * 111.274435518676) + 0.125207629209 := by gcongr
    _ ≤ (0.163331639374 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053378032505)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417092838) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284198221274) :
    parallelOracle 12382 0.011 xi bn cd ≤ 0.164351289144 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12382 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12382 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488818050 : ℝ) ≤ plow 12382 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.274435518676 : ℝ) ≤ √(12382 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284198221274 : ℝ) / (2 * 0.560488818050 * 111.274435518676)) * 0.163331639374 +
        0.284198221274 ^ 2 / (2 * 0.560488818050 * 111.274435518676) := by gcongr
    _ ≤ (0.164351289144 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053378032505) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001417092838)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284198221274) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12382 12382 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488818050 : ℝ) ≤ plow 12382 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.274435518676 : ℝ) ≤ √(12382 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12382 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12382 Θ 1.22 ≤ 0.011917386899 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.274435518676 := by gcongr <;> linarith
      _ ≤ (0.011917386899 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12382 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12382 12382 0.011 ≤ 0.008590356977 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12382 12382 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12382 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12382 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12382 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12382 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164351289144 + 0.011917386899 + (0.008590356977 : ℝ) *
        (1 + 2 * (0.284198221274 + 0.011917386899) / (0.560488818050 * 111.274435518676))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12382]

end BstLean.Part269.N12382

/-! The original eight local profiles supply actual 12382 moment certificates. -/
namespace BstLean.Part269.N12382
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12382 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12382 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12382 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053378032505 ∧
    0 ≤ bN 12382 BstLean.Part154.csC (groupTheta g) ∧ bN 12382 BstLean.Part154.csC (groupTheta g) ≤ 0.001417092838 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12382 12382 0.011
      (momentAllowance 12382 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12382 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12382 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12382 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12382 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12382 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231036863953 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12382 0.011
      (momentAllowance 12382 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12382 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12382
/-! The actual computed-centre upper energy formula at 12382. -/
namespace BstLean.Part269.N12382
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12382

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12382
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12382)
open BstLean.Part268 (cell12382)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086478987387
  | 2 => 0.087441369898
  | 3 => 0.088404985857
  | 4 => 0.089371947690
  | 5 => 0.090344784373
  | 6 => 0.091326499799
  | 7 => 0.092320636022
  | 8 => 0.093331341298
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12382 12382 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12382 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12382

/-! Actual upper energy certificates on all 43 source endpoints at 12382. -/
namespace BstLean.Part269.N12382
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12382)
open BstLean.Part268 (cell12382)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12382 (gMinus 12382) (1 - (cell12382 i).lower) ≤ 1 ∧
    energyUpper 12382 (gMinus 12382) (BstLean.Part211.gPlus 12382)
      (finiteEnergy 12382 12382 0.011) (1 - (cell12382 i).lower) ≤
      (cell12382 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨10,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨11,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨12,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨13,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨14,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨15,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨16,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨17,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨18,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨19,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨20,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨21,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨22,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨23,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨24,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨25,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨26,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨27,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨28,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨29,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨30,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨31,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨32,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨33,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨34,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨35,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨36,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨37,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨38,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨39,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨40,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨41,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨42,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨43,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨44,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨45,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨46,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨47,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨48,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨49,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨50,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨51,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12382) (by norm_num)
        (q := 1 - (cell12382 ⟨52,by decide⟩).lower)
        (by norm_num [cell12382]) (by norm_num [cell12382])
      exact ⟨E.1,E.2.trans (by norm_num [cell12382])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12382

/-! Source-cell containment and simple scalar guards at 12382. -/
namespace BstLean.Part269.N12382
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12382)
open BstLean.Part268 (cell12382)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12382 ⟨10,by decide⟩).lower ∧ (cell12382 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12382 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12382 ⟨11,by decide⟩).lower ∧ (cell12382 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12382 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12382 ⟨12,by decide⟩).lower ∧ (cell12382 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12382 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12382 ⟨13,by decide⟩).lower ∧ (cell12382 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12382 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12382 ⟨14,by decide⟩).lower ∧ (cell12382 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12382 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12382 ⟨15,by decide⟩).lower ∧ (cell12382 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12382 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12382 ⟨16,by decide⟩).lower ∧ (cell12382 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12382 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12382 ⟨17,by decide⟩).lower ∧ (cell12382 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12382 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12382 ⟨18,by decide⟩).lower ∧ (cell12382 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12382 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12382 ⟨19,by decide⟩).lower ∧ (cell12382 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12382 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12382 ⟨20,by decide⟩).lower ∧ (cell12382 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12382 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12382 ⟨21,by decide⟩).lower ∧ (cell12382 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12382 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12382 ⟨22,by decide⟩).lower ∧ (cell12382 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12382 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12382 ⟨23,by decide⟩).lower ∧ (cell12382 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12382 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12382 ⟨24,by decide⟩).lower ∧ (cell12382 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12382 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12382 ⟨25,by decide⟩).lower ∧ (cell12382 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12382 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12382 ⟨26,by decide⟩).lower ∧ (cell12382 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12382 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12382 ⟨27,by decide⟩).lower ∧ (cell12382 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12382 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12382 ⟨28,by decide⟩).lower ∧ (cell12382 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12382 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12382 ⟨29,by decide⟩).lower ∧ (cell12382 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12382 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12382 ⟨30,by decide⟩).lower ∧ (cell12382 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12382 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12382 ⟨31,by decide⟩).lower ∧ (cell12382 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12382 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12382 ⟨32,by decide⟩).lower ∧ (cell12382 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12382 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12382 ⟨33,by decide⟩).lower ∧ (cell12382 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12382 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12382 ⟨34,by decide⟩).lower ∧ (cell12382 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12382 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12382 ⟨35,by decide⟩).lower ∧ (cell12382 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12382 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12382 ⟨36,by decide⟩).lower ∧ (cell12382 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12382 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12382 ⟨37,by decide⟩).lower ∧ (cell12382 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12382 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12382 ⟨38,by decide⟩).lower ∧ (cell12382 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12382 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12382 ⟨39,by decide⟩).lower ∧ (cell12382 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12382 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12382 ⟨40,by decide⟩).lower ∧ (cell12382 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12382 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12382 ⟨41,by decide⟩).lower ∧ (cell12382 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12382 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12382 ⟨42,by decide⟩).lower ∧ (cell12382 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12382 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12382 ⟨43,by decide⟩).lower ∧ (cell12382 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12382 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12382 ⟨44,by decide⟩).lower ∧ (cell12382 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12382 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12382 ⟨45,by decide⟩).lower ∧ (cell12382 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12382 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12382 ⟨46,by decide⟩).lower ∧ (cell12382 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12382 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12382 ⟨47,by decide⟩).lower ∧ (cell12382 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12382 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12382 ⟨48,by decide⟩).lower ∧ (cell12382 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12382 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12382 ⟨49,by decide⟩).lower ∧ (cell12382 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12382 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12382 ⟨50,by decide⟩).lower ∧ (cell12382 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12382 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12382 ⟨51,by decide⟩).lower ∧ (cell12382 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12382 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12382 ⟨52,by decide⟩).lower ∧ (cell12382 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12382 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12382 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12382 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12382,cell12382,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12382 i).lower ∧
    (cell12382 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12382 i).upper ≤ (0.532 : ℝ) ∧
    (cell12382 i).centre ≤ (0.1 : ℝ) ∧ (cell12382 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12382 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12382 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12382

/-! The local source numeric instances at 12382 have no network premises. -/
namespace BstLean.Part269.N12382
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12382)
open BstLean.Part268 (cell12382)

noncomputable def sourceNumerics12382 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12382 (cell12382 i)
      scalarRow12382.M scalarRow12382.H scalarRow12382.xi := by
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
    energy_allowance := scalarRow12382.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12382]
    centre_nonneg := (scalarRow12382.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12382])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12382
/-! Actual 12383 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12383
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12383 ≤ (1.036268732561 : ℝ) := by
  have hr : (111.278928823025 : ℝ) ≤ √(12383 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.278928823025 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12383 12383 (11 / 1000) ≤
    (0.008590010106 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12383) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.278928823025 : ℝ) ≤ √(12383 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12383)
  have hdiv : K / √(12383 : ℝ) ≤ K / 111.278928823025 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.278928823025 ≤ (0.008590010106 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12383.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12383 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12383 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12383 := gPlus_lower 12383
end BstLean.Part269.N12383

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12383
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036268732560 : ℝ) ≤ wn 12383 := by
  have hn : √(12383 : ℝ) ≤ 111.278928823026 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12383 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.278928823026 ≤ 2 / √(12383 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258443523 : ℝ) ≤ rhoBar 12383 BstLean.Part154.csC ∧
    rhoBar 12383 BstLean.Part154.csC ≤ 0.000258443923 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036268732560 : ℝ) / (1.295212 * 12383) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036268732561 : ℝ) / (1.29521 * 12383) := by gcongr
      _ ≤ (0.000258443923 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12383 BstLean.Part154.csC) ≤ 0.001033842486 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12383 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12383 BstLean.Part154.csC) (piBar (rhoBar 12383 BstLean.Part154.csC)) ≤ 0.000197401451 ∧
    cc1 (rhoBar 12383 BstLean.Part154.csC) (piBar (rhoBar 12383 BstLean.Part154.csC)) ≤ 0.000125607805 ∧
    cc2 (rhoBar 12383 BstLean.Part154.csC) ≤ 0.000072916233 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12383 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12383 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12383 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12383 BstLean.Part154.csC * nuR (rhoBar 12383 BstLean.Part154.csC)) ≤ 0.000516904545 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258443923 : ℝ) * 0.001033842486 := by gcongr
      _ ≤ (0.000516904545 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12383 BstLean.Part154.csC) * nuR (rhoBar 12383 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001033842486 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12383 BstLean.Part154.csC) * rhoBar 12383 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258443923 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258443923 / 2 + 0.399 * 0.001033842486 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197401451 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516904545 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125607805 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258443923 / 1.414213562 := by gcongr
      _ ≤ (0.000072916233 : ℝ) := by norm_num

end BstLean.Part269.N12383

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12383
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12383 BstLean.Part154.csC) (piBar (rhoBar 12383 BstLean.Part154.csC)) ≤ 1.68281E-7 := by
  have hr0 : 0 ≤ rhoBar 12383 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12383 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12383 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12383 BstLean.Part154.csC) (piBar (rhoBar 12383 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12383 BstLean.Part154.csC) (piBar (rhoBar 12383 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12383 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197401451 : ℝ) ^ 2 + 0.000125607805 ^ 2 + 3 * 0.000072916233 ^ 2 +
        2 * 0.797885 * 0.000197401451 * 0.000125607805 + 2 * 0.000197401451 * 0.000072916233 +
        4 * 0.797885 * 0.000125607805 * 0.000072916233 := by gcongr
    _ ≤ (1.68281E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12383 BstLean.Part154.csC Θ ≤ 0.002698993368 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12383 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12383 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12383 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12383 BstLean.Part154.csC) (piBar (rhoBar 12383 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12383 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036268732561 * 1.68281E-7 / (0.000258443523 : ℝ) := by gcongr
    _ ≤ 0.002698993368 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12383 BstLean.Part154.csC Θ ≤ 0.002996009427 + 0.000681991441 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12383 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12383 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12383 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036268732561 : ℝ) * ((2 * Θ * 0.000258443923 +
        (6863 / 10000) * 0.000258443923 * 12383 * 0.001033842486) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002996009427 + 0.000681991441 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12383 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12383 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12383 0.011 Θ ∧ gammaRatio 12383 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12383 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036268732561 : ℝ) * 0.525 / ((1 - 0.011) * 12383) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12383 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12383 0.011 Θ) :=
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
    badAllowance 12383 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12383 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12383 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12383 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12383 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12383 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12383 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12383 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12383 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12383 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12383 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036268732561 : ℝ) * 12383 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12383 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004096009427 + 0.003380984809 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12383

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12383
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12383 BstLean.Part154.csC) (piBar (rhoBar 12383 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12383 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12383 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12383 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12383 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12383 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12383 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12383 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12383 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12383 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12383 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12383 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12383 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12383 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12383 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053159187165 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12383) ≤ 0.010731929160 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12383 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036268732561)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010731929160 + 2 * 0.737676 / 12383) := by gcongr
    _ ≤ (0.053159187165 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12383 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12383

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12383
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488865622 : ℝ) ≤ plow 12383 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12383) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053377626452)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416971519) : eMP 12383 0.011 xi bn ≤ 0.001219490289 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12383 : ℝ) * (1 - 0.011))) ≤ 0.000602898827 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001416971519 / (12383 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602898827 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602898827 : ℝ) + 3.141593 * 0.053377626452 / (12383 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001219490289 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053377626452)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416971519) : PiBarMP 12383 12 0.011 xi bn ≤ 0.163324945155 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12383 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037642682145 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.665202299548 : ℝ) ≤ √((12383 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.278928823025 : ℝ) ≤ √(12383 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12383) ≤ 0.125202573481 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037642682145 + 0.053377626452 * 1.772454 / (2 * (110.665202299548 : ℝ))) * (1 + 0.001219490289) +
        8 / (12383 * 111.278928823025) + 0.125202573481 := by gcongr
    _ ≤ (0.163324945155 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053377626452)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416971519) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284195172354) :
    parallelOracle 12383 0.011 xi bn cd ≤ 0.164344520530 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12383 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12383 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488865622 : ℝ) ≤ plow 12383 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.278928823025 : ℝ) ≤ √(12383 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284195172354 : ℝ) / (2 * 0.560488865622 * 111.278928823025)) * 0.163324945155 +
        0.284195172354 ^ 2 / (2 * 0.560488865622 * 111.278928823025) := by gcongr
    _ ≤ (0.164344520530 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053377626452) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416971519)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284195172354) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12383 12383 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488865622 : ℝ) ≤ plow 12383 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.278928823025 : ℝ) ≤ √(12383 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12383 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12383 Θ 1.22 ≤ 0.011916905690 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.278928823025 := by gcongr <;> linarith
      _ ≤ (0.011916905690 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12383 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12383 12383 0.011 ≤ 0.008590010106 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12383 12383 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12383 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12383 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12383 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12383 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164344520530 + 0.011916905690 + (0.008590010106 : ℝ) *
        (1 + 2 * (0.284195172354 + 0.011916905690) / (0.560488865622 * 111.278928823025))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12383]

end BstLean.Part269.N12383

/-! The original eight local profiles supply actual 12383 moment certificates. -/
namespace BstLean.Part269.N12383
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12383 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12383 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12383 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053377626452 ∧
    0 ≤ bN 12383 BstLean.Part154.csC (groupTheta g) ∧ bN 12383 BstLean.Part154.csC (groupTheta g) ≤ 0.001416971519 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12383 12383 0.011
      (momentAllowance 12383 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12383 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12383 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12383 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12383 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12383 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231035985189 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12383 0.011
      (momentAllowance 12383 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12383 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12383
/-! The actual computed-centre upper energy formula at 12383. -/
namespace BstLean.Part269.N12383
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12383

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12383
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12383)
open BstLean.Part268 (cell12383)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086475663170
  | 2 => 0.087437974601
  | 3 => 0.088401507570
  | 4 => 0.089368371889
  | 5 => 0.090341093479
  | 6 => 0.091322672695
  | 7 => 0.092316647505
  | 8 => 0.093327161486
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12383 12383 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12383 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12383

/-! Actual upper energy certificates on all 43 source endpoints at 12383. -/
namespace BstLean.Part269.N12383
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12383)
open BstLean.Part268 (cell12383)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12383 (gMinus 12383) (1 - (cell12383 i).lower) ≤ 1 ∧
    energyUpper 12383 (gMinus 12383) (BstLean.Part211.gPlus 12383)
      (finiteEnergy 12383 12383 0.011) (1 - (cell12383 i).lower) ≤
      (cell12383 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨10,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨11,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨12,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨13,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨14,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨15,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨16,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨17,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨18,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨19,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨20,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨21,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨22,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨23,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨24,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨25,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨26,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨27,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨28,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨29,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨30,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨31,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨32,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨33,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨34,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨35,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨36,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨37,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨38,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨39,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨40,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨41,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨42,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨43,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨44,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨45,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨46,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨47,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨48,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨49,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨50,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨51,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12383) (by norm_num)
        (q := 1 - (cell12383 ⟨52,by decide⟩).lower)
        (by norm_num [cell12383]) (by norm_num [cell12383])
      exact ⟨E.1,E.2.trans (by norm_num [cell12383])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12383

/-! Source-cell containment and simple scalar guards at 12383. -/
namespace BstLean.Part269.N12383
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12383)
open BstLean.Part268 (cell12383)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12383 ⟨10,by decide⟩).lower ∧ (cell12383 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12383 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12383 ⟨11,by decide⟩).lower ∧ (cell12383 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12383 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12383 ⟨12,by decide⟩).lower ∧ (cell12383 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12383 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12383 ⟨13,by decide⟩).lower ∧ (cell12383 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12383 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12383 ⟨14,by decide⟩).lower ∧ (cell12383 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12383 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12383 ⟨15,by decide⟩).lower ∧ (cell12383 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12383 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12383 ⟨16,by decide⟩).lower ∧ (cell12383 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12383 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12383 ⟨17,by decide⟩).lower ∧ (cell12383 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12383 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12383 ⟨18,by decide⟩).lower ∧ (cell12383 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12383 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12383 ⟨19,by decide⟩).lower ∧ (cell12383 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12383 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12383 ⟨20,by decide⟩).lower ∧ (cell12383 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12383 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12383 ⟨21,by decide⟩).lower ∧ (cell12383 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12383 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12383 ⟨22,by decide⟩).lower ∧ (cell12383 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12383 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12383 ⟨23,by decide⟩).lower ∧ (cell12383 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12383 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12383 ⟨24,by decide⟩).lower ∧ (cell12383 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12383 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12383 ⟨25,by decide⟩).lower ∧ (cell12383 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12383 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12383 ⟨26,by decide⟩).lower ∧ (cell12383 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12383 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12383 ⟨27,by decide⟩).lower ∧ (cell12383 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12383 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12383 ⟨28,by decide⟩).lower ∧ (cell12383 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12383 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12383 ⟨29,by decide⟩).lower ∧ (cell12383 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12383 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12383 ⟨30,by decide⟩).lower ∧ (cell12383 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12383 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12383 ⟨31,by decide⟩).lower ∧ (cell12383 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12383 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12383 ⟨32,by decide⟩).lower ∧ (cell12383 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12383 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12383 ⟨33,by decide⟩).lower ∧ (cell12383 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12383 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12383 ⟨34,by decide⟩).lower ∧ (cell12383 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12383 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12383 ⟨35,by decide⟩).lower ∧ (cell12383 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12383 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12383 ⟨36,by decide⟩).lower ∧ (cell12383 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12383 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12383 ⟨37,by decide⟩).lower ∧ (cell12383 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12383 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12383 ⟨38,by decide⟩).lower ∧ (cell12383 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12383 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12383 ⟨39,by decide⟩).lower ∧ (cell12383 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12383 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12383 ⟨40,by decide⟩).lower ∧ (cell12383 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12383 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12383 ⟨41,by decide⟩).lower ∧ (cell12383 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12383 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12383 ⟨42,by decide⟩).lower ∧ (cell12383 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12383 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12383 ⟨43,by decide⟩).lower ∧ (cell12383 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12383 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12383 ⟨44,by decide⟩).lower ∧ (cell12383 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12383 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12383 ⟨45,by decide⟩).lower ∧ (cell12383 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12383 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12383 ⟨46,by decide⟩).lower ∧ (cell12383 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12383 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12383 ⟨47,by decide⟩).lower ∧ (cell12383 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12383 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12383 ⟨48,by decide⟩).lower ∧ (cell12383 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12383 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12383 ⟨49,by decide⟩).lower ∧ (cell12383 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12383 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12383 ⟨50,by decide⟩).lower ∧ (cell12383 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12383 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12383 ⟨51,by decide⟩).lower ∧ (cell12383 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12383 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12383 ⟨52,by decide⟩).lower ∧ (cell12383 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12383 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12383 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12383 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12383,cell12383,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12383 i).lower ∧
    (cell12383 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12383 i).upper ≤ (0.532 : ℝ) ∧
    (cell12383 i).centre ≤ (0.1 : ℝ) ∧ (cell12383 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12383 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12383 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12383

/-! The local source numeric instances at 12383 have no network premises. -/
namespace BstLean.Part269.N12383
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12383)
open BstLean.Part268 (cell12383)

noncomputable def sourceNumerics12383 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12383 (cell12383 i)
      scalarRow12383.M scalarRow12383.H scalarRow12383.xi := by
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
    energy_allowance := scalarRow12383.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12383]
    centre_nonneg := (scalarRow12383.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12383])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12383
/-! Actual 12384 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12384
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12384 ≤ (1.036267255151 : ℝ) := by
  have hr : (111.283421945948 : ℝ) ≤ √(12384 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.283421945948 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12384 12384 (11 / 1000) ≤
    (0.008589663278 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12384) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.283421945948 : ℝ) ≤ √(12384 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12384)
  have hdiv : K / √(12384 : ℝ) ≤ K / 111.283421945948 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.283421945948 ≤ (0.008589663278 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12384.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12384 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12384 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12384 := gPlus_lower 12384
end BstLean.Part269.N12384

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12384
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036267255150 : ℝ) ≤ wn 12384 := by
  have hn : √(12384 : ℝ) ≤ 111.283421945949 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12384 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.283421945949 ≤ 2 / √(12384 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258422285 : ℝ) ≤ rhoBar 12384 BstLean.Part154.csC ∧
    rhoBar 12384 BstLean.Part154.csC ≤ 0.000258422685 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036267255150 : ℝ) / (1.295212 * 12384) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036267255151 : ℝ) / (1.29521 * 12384) := by gcongr
      _ ≤ (0.000258422685 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12384 BstLean.Part154.csC) ≤ 0.001033757523 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12384 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12384 BstLean.Part154.csC) (piBar (rhoBar 12384 BstLean.Part154.csC)) ≤ 0.000197385229 ∧
    cc1 (rhoBar 12384 BstLean.Part154.csC) (piBar (rhoBar 12384 BstLean.Part154.csC)) ≤ 0.000125597483 ∧
    cc2 (rhoBar 12384 BstLean.Part154.csC) ≤ 0.000072910241 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12384 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12384 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12384 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12384 BstLean.Part154.csC * nuR (rhoBar 12384 BstLean.Part154.csC)) ≤ 0.000516862066 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258422685 : ℝ) * 0.001033757523 := by gcongr
      _ ≤ (0.000516862066 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12384 BstLean.Part154.csC) * nuR (rhoBar 12384 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001033757523 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12384 BstLean.Part154.csC) * rhoBar 12384 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258422685 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258422685 / 2 + 0.399 * 0.001033757523 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197385229 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516862066 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125597483 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258422685 / 1.414213562 := by gcongr
      _ ≤ (0.000072910241 : ℝ) := by norm_num

end BstLean.Part269.N12384

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12384
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12384 BstLean.Part154.csC) (piBar (rhoBar 12384 BstLean.Part154.csC)) ≤ 1.68254E-7 := by
  have hr0 : 0 ≤ rhoBar 12384 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12384 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12384 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12384 BstLean.Part154.csC) (piBar (rhoBar 12384 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12384 BstLean.Part154.csC) (piBar (rhoBar 12384 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12384 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197385229 : ℝ) ^ 2 + 0.000125597483 ^ 2 + 3 * 0.000072910241 ^ 2 +
        2 * 0.797885 * 0.000197385229 * 0.000125597483 + 2 * 0.000197385229 * 0.000072910241 +
        4 * 0.797885 * 0.000125597483 * 0.000072910241 := by gcongr
    _ ≤ (1.68254E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12384 BstLean.Part154.csC Θ ≤ 0.002698778254 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12384 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12384 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12384 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12384 BstLean.Part154.csC) (piBar (rhoBar 12384 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12384 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036267255151 * 1.68254E-7 / (0.000258422285 : ℝ) := by gcongr
    _ ≤ 0.002698778254 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12384 BstLean.Part154.csC Θ ≤ 0.002995754663 + 0.000681934425 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12384 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12384 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12384 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036267255151 : ℝ) * ((2 * Θ * 0.000258422685 +
        (6863 / 10000) * 0.000258422685 * 12384 * 0.001033757523) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002995754663 + 0.000681934425 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12384 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12384 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12384 0.011 Θ ∧ gammaRatio 12384 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12384 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036267255151 : ℝ) * 0.525 / ((1 - 0.011) * 12384) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12384 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12384 0.011 Θ) :=
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
    badAllowance 12384 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12384 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12384 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12384 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12384 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12384 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12384 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12384 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12384 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12384 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12384 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036267255151 : ℝ) * 12384 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12384 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004095754663 + 0.003380712679 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12384

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12384
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12384 BstLean.Part154.csC) (piBar (rhoBar 12384 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12384 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12384 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12384 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12384 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12384 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12384 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12384 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12384 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12384 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12384 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12384 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12384 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12384 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12384 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053157017271 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12384) ≤ 0.010731495853 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12384 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036267255151)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010731495853 + 2 * 0.737676 / 12384) := by gcongr
    _ ≤ (0.053157017271 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12384 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12384

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12384
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488913186 : ℝ) ≤ plow 12384 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12384) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053377228820)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416858584) : eMP 12384 0.011 xi bn ≤ 0.001219392345 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12384 : ℝ) * (1 - 0.011))) ≤ 0.000602850459 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001416858584 / (12384 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602850459 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602850459 : ℝ) + 3.141593 * 0.053377228820 / (12384 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001219392345 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053377228820)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416858584) : PiBarMP 12384 12 0.011 xi bn ≤ 0.163318363187 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12384 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037641182022 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.669670641960 : ℝ) ≤ √((12384 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.283421945948 : ℝ) ≤ √(12384 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12384) ≤ 0.125197518365 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037641182022 + 0.053377228820 * 1.772454 / (2 * (110.669670641960 : ℝ))) * (1 + 0.001219392345) +
        8 / (12384 * 111.283421945948) + 0.125197518365 := by gcongr
    _ ≤ (0.163318363187 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053377228820)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416858584) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284192141917) :
    parallelOracle 12384 0.011 xi bn cd ≤ 0.164337864540 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12384 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12384 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488913186 : ℝ) ≤ plow 12384 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.283421945948 : ℝ) ≤ √(12384 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284192141917 : ℝ) / (2 * 0.560488913186 * 111.283421945948)) * 0.163318363187 +
        0.284192141917 ^ 2 / (2 * 0.560488913186 * 111.283421945948) := by gcongr
    _ ≤ (0.164337864540 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053377228820) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416858584)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284192141917) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12384 12384 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488913186 : ℝ) ≤ plow 12384 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.283421945948 : ℝ) ≤ √(12384 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12384 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12384 Θ 1.22 ≤ 0.011916424539 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.283421945948 := by gcongr <;> linarith
      _ ≤ (0.011916424539 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12384 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12384 12384 0.011 ≤ 0.008589663278 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12384 12384 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12384 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12384 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12384 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12384 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164337864540 + 0.011916424539 + (0.008589663278 : ℝ) *
        (1 + 2 * (0.284192141917 + 0.011916424539) / (0.560488913186 * 111.283421945948))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12384]

end BstLean.Part269.N12384

/-! The original eight local profiles supply actual 12384 moment certificates. -/
namespace BstLean.Part269.N12384
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12384 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12384 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12384 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053377228820 ∧
    0 ≤ bN 12384 BstLean.Part154.csC (groupTheta g) ∧ bN 12384 BstLean.Part154.csC (groupTheta g) ≤ 0.001416858584 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12384 12384 0.011
      (momentAllowance 12384 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12384 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12384 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12384 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12384 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12384 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231035124646 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12384 0.011
      (momentAllowance 12384 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12384 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12384
/-! The actual computed-centre upper energy formula at 12384. -/
namespace BstLean.Part269.N12384
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12384

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12384
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12384)
open BstLean.Part268 (cell12384)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086472340468
  | 2 => 0.087434580887
  | 3 => 0.088398030948
  | 4 => 0.089364797854
  | 5 => 0.090337404476
  | 6 => 0.091318847631
  | 7 => 0.092312661209
  | 8 => 0.093322984112
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12384 12384 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12384 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12384

/-! Actual upper energy certificates on all 43 source endpoints at 12384. -/
namespace BstLean.Part269.N12384
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12384)
open BstLean.Part268 (cell12384)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12384 (gMinus 12384) (1 - (cell12384 i).lower) ≤ 1 ∧
    energyUpper 12384 (gMinus 12384) (BstLean.Part211.gPlus 12384)
      (finiteEnergy 12384 12384 0.011) (1 - (cell12384 i).lower) ≤
      (cell12384 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨10,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨11,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨12,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨13,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨14,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨15,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨16,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨17,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨18,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨19,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨20,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨21,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨22,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨23,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨24,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨25,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨26,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨27,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨28,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨29,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨30,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨31,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨32,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨33,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨34,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨35,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨36,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨37,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨38,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨39,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨40,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨41,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨42,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨43,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨44,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨45,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨46,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨47,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨48,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨49,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨50,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨51,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12384) (by norm_num)
        (q := 1 - (cell12384 ⟨52,by decide⟩).lower)
        (by norm_num [cell12384]) (by norm_num [cell12384])
      exact ⟨E.1,E.2.trans (by norm_num [cell12384])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12384

/-! Source-cell containment and simple scalar guards at 12384. -/
namespace BstLean.Part269.N12384
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12384)
open BstLean.Part268 (cell12384)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12384 ⟨10,by decide⟩).lower ∧ (cell12384 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12384 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12384 ⟨11,by decide⟩).lower ∧ (cell12384 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12384 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12384 ⟨12,by decide⟩).lower ∧ (cell12384 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12384 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12384 ⟨13,by decide⟩).lower ∧ (cell12384 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12384 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12384 ⟨14,by decide⟩).lower ∧ (cell12384 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12384 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12384 ⟨15,by decide⟩).lower ∧ (cell12384 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12384 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12384 ⟨16,by decide⟩).lower ∧ (cell12384 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12384 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12384 ⟨17,by decide⟩).lower ∧ (cell12384 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12384 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12384 ⟨18,by decide⟩).lower ∧ (cell12384 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12384 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12384 ⟨19,by decide⟩).lower ∧ (cell12384 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12384 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12384 ⟨20,by decide⟩).lower ∧ (cell12384 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12384 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12384 ⟨21,by decide⟩).lower ∧ (cell12384 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12384 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12384 ⟨22,by decide⟩).lower ∧ (cell12384 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12384 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12384 ⟨23,by decide⟩).lower ∧ (cell12384 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12384 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12384 ⟨24,by decide⟩).lower ∧ (cell12384 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12384 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12384 ⟨25,by decide⟩).lower ∧ (cell12384 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12384 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12384 ⟨26,by decide⟩).lower ∧ (cell12384 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12384 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12384 ⟨27,by decide⟩).lower ∧ (cell12384 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12384 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12384 ⟨28,by decide⟩).lower ∧ (cell12384 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12384 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12384 ⟨29,by decide⟩).lower ∧ (cell12384 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12384 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12384 ⟨30,by decide⟩).lower ∧ (cell12384 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12384 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12384 ⟨31,by decide⟩).lower ∧ (cell12384 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12384 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12384 ⟨32,by decide⟩).lower ∧ (cell12384 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12384 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12384 ⟨33,by decide⟩).lower ∧ (cell12384 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12384 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12384 ⟨34,by decide⟩).lower ∧ (cell12384 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12384 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12384 ⟨35,by decide⟩).lower ∧ (cell12384 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12384 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12384 ⟨36,by decide⟩).lower ∧ (cell12384 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12384 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12384 ⟨37,by decide⟩).lower ∧ (cell12384 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12384 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12384 ⟨38,by decide⟩).lower ∧ (cell12384 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12384 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12384 ⟨39,by decide⟩).lower ∧ (cell12384 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12384 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12384 ⟨40,by decide⟩).lower ∧ (cell12384 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12384 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12384 ⟨41,by decide⟩).lower ∧ (cell12384 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12384 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12384 ⟨42,by decide⟩).lower ∧ (cell12384 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12384 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12384 ⟨43,by decide⟩).lower ∧ (cell12384 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12384 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12384 ⟨44,by decide⟩).lower ∧ (cell12384 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12384 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12384 ⟨45,by decide⟩).lower ∧ (cell12384 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12384 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12384 ⟨46,by decide⟩).lower ∧ (cell12384 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12384 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12384 ⟨47,by decide⟩).lower ∧ (cell12384 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12384 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12384 ⟨48,by decide⟩).lower ∧ (cell12384 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12384 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12384 ⟨49,by decide⟩).lower ∧ (cell12384 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12384 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12384 ⟨50,by decide⟩).lower ∧ (cell12384 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12384 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12384 ⟨51,by decide⟩).lower ∧ (cell12384 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12384 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12384 ⟨52,by decide⟩).lower ∧ (cell12384 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12384 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12384 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12384 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12384,cell12384,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12384 i).lower ∧
    (cell12384 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12384 i).upper ≤ (0.532 : ℝ) ∧
    (cell12384 i).centre ≤ (0.1 : ℝ) ∧ (cell12384 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12384 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12384 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12384

/-! The local source numeric instances at 12384 have no network premises. -/
namespace BstLean.Part269.N12384
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12384)
open BstLean.Part268 (cell12384)

noncomputable def sourceNumerics12384 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12384 (cell12384 i)
      scalarRow12384.M scalarRow12384.H scalarRow12384.xi := by
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
    energy_allowance := scalarRow12384.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12384]
    centre_nonneg := (scalarRow12384.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12384])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12384
/-! Actual 12385 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12385
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12385 ≤ (1.036265777921 : ℝ) := by
  have hr : (111.287914887466 : ℝ) ≤ √(12385 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.287914887466 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12385 12385 (11 / 1000) ≤
    (0.008589316491 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12385) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.287914887466 : ℝ) ≤ √(12385 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12385)
  have hdiv : K / √(12385 : ℝ) ≤ K / 111.287914887466 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.287914887466 ≤ (0.008589316491 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12385.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12385 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12385 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12385 := gPlus_lower 12385
end BstLean.Part269.N12385

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12385
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036265777920 : ℝ) ≤ wn 12385 := by
  have hn : √(12385 : ℝ) ≤ 111.287914887467 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12385 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.287914887467 ≤ 2 / √(12385 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258401051 : ℝ) ≤ rhoBar 12385 BstLean.Part154.csC ∧
    rhoBar 12385 BstLean.Part154.csC ≤ 0.000258401451 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036265777920 : ℝ) / (1.295212 * 12385) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036265777921 : ℝ) / (1.29521 * 12385) := by gcongr
      _ ≤ (0.000258401451 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12385 BstLean.Part154.csC) ≤ 0.001033672576 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12385 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12385 BstLean.Part154.csC) (piBar (rhoBar 12385 BstLean.Part154.csC)) ≤ 0.000197369009 ∧
    cc1 (rhoBar 12385 BstLean.Part154.csC) (piBar (rhoBar 12385 BstLean.Part154.csC)) ≤ 0.000125587162 ∧
    cc2 (rhoBar 12385 BstLean.Part154.csC) ≤ 0.000072904250 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12385 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12385 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12385 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12385 BstLean.Part154.csC * nuR (rhoBar 12385 BstLean.Part154.csC)) ≤ 0.000516819595 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258401451 : ℝ) * 0.001033672576 := by gcongr
      _ ≤ (0.000516819595 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12385 BstLean.Part154.csC) * nuR (rhoBar 12385 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001033672576 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12385 BstLean.Part154.csC) * rhoBar 12385 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258401451 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258401451 / 2 + 0.399 * 0.001033672576 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197369009 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516819595 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125587162 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258401451 / 1.414213562 := by gcongr
      _ ≤ (0.000072904250 : ℝ) := by norm_num

end BstLean.Part269.N12385

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12385
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12385 BstLean.Part154.csC) (piBar (rhoBar 12385 BstLean.Part154.csC)) ≤ 1.68226E-7 := by
  have hr0 : 0 ≤ rhoBar 12385 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12385 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12385 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12385 BstLean.Part154.csC) (piBar (rhoBar 12385 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12385 BstLean.Part154.csC) (piBar (rhoBar 12385 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12385 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197369009 : ℝ) ^ 2 + 0.000125587162 ^ 2 + 3 * 0.000072904250 ^ 2 +
        2 * 0.797885 * 0.000197369009 * 0.000125587162 + 2 * 0.000197369009 * 0.000072904250 +
        4 * 0.797885 * 0.000125587162 * 0.000072904250 := by gcongr
    _ ≤ (1.68226E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12385 BstLean.Part154.csC Θ ≤ 0.002698547024 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12385 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12385 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12385 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12385 BstLean.Part154.csC) (piBar (rhoBar 12385 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12385 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036265777921 * 1.68226E-7 / (0.000258401051 : ℝ) := by gcongr
    _ ≤ 0.002698547024 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12385 BstLean.Part154.csC Θ ≤ 0.002995499954 + 0.000681877420 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12385 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12385 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12385 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036265777921 : ℝ) * ((2 * Θ * 0.000258401451 +
        (6863 / 10000) * 0.000258401451 * 12385 * 0.001033672576) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002995499954 + 0.000681877420 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12385 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12385 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12385 0.011 Θ ∧ gammaRatio 12385 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12385 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036265777921 : ℝ) * 0.525 / ((1 - 0.011) * 12385) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12385 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12385 0.011 Θ) :=
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
    badAllowance 12385 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12385 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12385 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12385 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12385 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12385 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12385 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12385 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12385 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12385 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12385 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036265777921 : ℝ) * 12385 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12385 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004095499954 + 0.003380424444 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12385

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12385
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12385 BstLean.Part154.csC) (piBar (rhoBar 12385 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12385 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12385 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12385 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12385 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12385 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12385 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12385 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12385 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12385 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12385 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12385 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12385 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12385 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12385 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053154847639 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12385) ≤ 0.010731062598 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12385 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036265777921)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010731062598 + 2 * 0.737676 / 12385) := by gcongr
    _ ≤ (0.053154847639 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12385 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12385

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12385
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560488960742 : ℝ) ≤ plow 12385 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12385) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053376822788)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416737188) : eMP 12385 0.011 xi bn ≤ 0.001219290808 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12385 : ℝ) * (1 - 0.011))) ≤ 0.000602800295 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001416737188 / (12385 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602800295 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602800295 : ℝ) + 3.141593 * 0.053376822788 / (12385 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001219290808 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053376822788)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416737188) : PiBarMP 12385 12 0.011 xi bn ≤ 0.163311669039 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12385 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037639569445 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.674138803968 : ℝ) ≤ √((12385 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.287914887466 : ℝ) ≤ √(12385 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12385) ≤ 0.125192463862 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037639569445 + 0.053376822788 * 1.772454 / (2 * (110.674138803968 : ℝ))) * (1 + 0.001219290808) +
        8 / (12385 * 111.287914887466) + 0.125192463862 := by gcongr
    _ ≤ (0.163311669039 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053376822788)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416737188) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284189093560) :
    parallelOracle 12385 0.011 xi bn cd ≤ 0.164331096017 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12385 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12385 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560488960742 : ℝ) ≤ plow 12385 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.287914887466 : ℝ) ≤ √(12385 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284189093560 : ℝ) / (2 * 0.560488960742 * 111.287914887466)) * 0.163311669039 +
        0.284189093560 ^ 2 / (2 * 0.560488960742 * 111.287914887466) := by gcongr
    _ ≤ (0.164331096017 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053376822788) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416737188)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284189093560) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12385 12385 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560488960742 : ℝ) ≤ plow 12385 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.287914887466 : ℝ) ≤ √(12385 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12385 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12385 Θ 1.22 ≤ 0.011915943446 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.287914887466 := by gcongr <;> linarith
      _ ≤ (0.011915943446 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12385 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12385 12385 0.011 ≤ 0.008589316491 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12385 12385 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12385 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12385 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12385 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12385 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164331096017 + 0.011915943446 + (0.008589316491 : ℝ) *
        (1 + 2 * (0.284189093560 + 0.011915943446) / (0.560488960742 * 111.287914887466))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12385]

end BstLean.Part269.N12385

/-! The original eight local profiles supply actual 12385 moment certificates. -/
namespace BstLean.Part269.N12385
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12385 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12385 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12385 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053376822788 ∧
    0 ≤ bN 12385 BstLean.Part154.csC (groupTheta g) ∧ bN 12385 BstLean.Part154.csC (groupTheta g) ≤ 0.001416737188 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12385 12385 0.011
      (momentAllowance 12385 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12385 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12385 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12385 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12385 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12385 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231034245921 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12385 0.011
      (momentAllowance 12385 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12385 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12385
/-! The actual computed-centre upper energy formula at 12385. -/
namespace BstLean.Part269.N12385
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12385

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12385
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12385)
open BstLean.Part268 (cell12385)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086469019278
  | 2 => 0.087431188752
  | 3 => 0.088394555989
  | 4 => 0.089361225583
  | 5 => 0.090333717362
  | 6 => 0.091315024606
  | 7 => 0.092308677132
  | 8 => 0.093318809172
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12385 12385 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12385 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12385

/-! Actual upper energy certificates on all 43 source endpoints at 12385. -/
namespace BstLean.Part269.N12385
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12385)
open BstLean.Part268 (cell12385)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12385 (gMinus 12385) (1 - (cell12385 i).lower) ≤ 1 ∧
    energyUpper 12385 (gMinus 12385) (BstLean.Part211.gPlus 12385)
      (finiteEnergy 12385 12385 0.011) (1 - (cell12385 i).lower) ≤
      (cell12385 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨10,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨11,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨12,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨13,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨14,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨15,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨16,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨17,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨18,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨19,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨20,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨21,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨22,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨23,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨24,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨25,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨26,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨27,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨28,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨29,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨30,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨31,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨32,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨33,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨34,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨35,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨36,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨37,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨38,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨39,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨40,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨41,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨42,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨43,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨44,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨45,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨46,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨47,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨48,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨49,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨50,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨51,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12385) (by norm_num)
        (q := 1 - (cell12385 ⟨52,by decide⟩).lower)
        (by norm_num [cell12385]) (by norm_num [cell12385])
      exact ⟨E.1,E.2.trans (by norm_num [cell12385])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12385

/-! Source-cell containment and simple scalar guards at 12385. -/
namespace BstLean.Part269.N12385
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12385)
open BstLean.Part268 (cell12385)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12385 ⟨10,by decide⟩).lower ∧ (cell12385 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12385 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12385 ⟨11,by decide⟩).lower ∧ (cell12385 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12385 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12385 ⟨12,by decide⟩).lower ∧ (cell12385 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12385 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12385 ⟨13,by decide⟩).lower ∧ (cell12385 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12385 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12385 ⟨14,by decide⟩).lower ∧ (cell12385 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12385 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12385 ⟨15,by decide⟩).lower ∧ (cell12385 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12385 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12385 ⟨16,by decide⟩).lower ∧ (cell12385 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12385 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12385 ⟨17,by decide⟩).lower ∧ (cell12385 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12385 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12385 ⟨18,by decide⟩).lower ∧ (cell12385 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12385 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12385 ⟨19,by decide⟩).lower ∧ (cell12385 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12385 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12385 ⟨20,by decide⟩).lower ∧ (cell12385 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12385 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12385 ⟨21,by decide⟩).lower ∧ (cell12385 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12385 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12385 ⟨22,by decide⟩).lower ∧ (cell12385 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12385 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12385 ⟨23,by decide⟩).lower ∧ (cell12385 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12385 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12385 ⟨24,by decide⟩).lower ∧ (cell12385 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12385 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12385 ⟨25,by decide⟩).lower ∧ (cell12385 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12385 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12385 ⟨26,by decide⟩).lower ∧ (cell12385 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12385 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12385 ⟨27,by decide⟩).lower ∧ (cell12385 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12385 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12385 ⟨28,by decide⟩).lower ∧ (cell12385 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12385 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12385 ⟨29,by decide⟩).lower ∧ (cell12385 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12385 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12385 ⟨30,by decide⟩).lower ∧ (cell12385 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12385 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12385 ⟨31,by decide⟩).lower ∧ (cell12385 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12385 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12385 ⟨32,by decide⟩).lower ∧ (cell12385 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12385 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12385 ⟨33,by decide⟩).lower ∧ (cell12385 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12385 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12385 ⟨34,by decide⟩).lower ∧ (cell12385 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12385 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12385 ⟨35,by decide⟩).lower ∧ (cell12385 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12385 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12385 ⟨36,by decide⟩).lower ∧ (cell12385 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12385 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12385 ⟨37,by decide⟩).lower ∧ (cell12385 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12385 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12385 ⟨38,by decide⟩).lower ∧ (cell12385 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12385 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12385 ⟨39,by decide⟩).lower ∧ (cell12385 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12385 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12385 ⟨40,by decide⟩).lower ∧ (cell12385 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12385 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12385 ⟨41,by decide⟩).lower ∧ (cell12385 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12385 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12385 ⟨42,by decide⟩).lower ∧ (cell12385 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12385 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12385 ⟨43,by decide⟩).lower ∧ (cell12385 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12385 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12385 ⟨44,by decide⟩).lower ∧ (cell12385 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12385 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12385 ⟨45,by decide⟩).lower ∧ (cell12385 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12385 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12385 ⟨46,by decide⟩).lower ∧ (cell12385 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12385 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12385 ⟨47,by decide⟩).lower ∧ (cell12385 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12385 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12385 ⟨48,by decide⟩).lower ∧ (cell12385 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12385 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12385 ⟨49,by decide⟩).lower ∧ (cell12385 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12385 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12385 ⟨50,by decide⟩).lower ∧ (cell12385 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12385 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12385 ⟨51,by decide⟩).lower ∧ (cell12385 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12385 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12385 ⟨52,by decide⟩).lower ∧ (cell12385 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12385 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12385 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12385 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12385,cell12385,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12385 i).lower ∧
    (cell12385 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12385 i).upper ≤ (0.532 : ℝ) ∧
    (cell12385 i).centre ≤ (0.1 : ℝ) ∧ (cell12385 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12385 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12385 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12385

/-! The local source numeric instances at 12385 have no network premises. -/
namespace BstLean.Part269.N12385
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12385)
open BstLean.Part268 (cell12385)

noncomputable def sourceNumerics12385 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12385 (cell12385 i)
      scalarRow12385.M scalarRow12385.H scalarRow12385.xi := by
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
    energy_allowance := scalarRow12385.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12385]
    centre_nonneg := (scalarRow12385.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12385])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12385
/-! Actual 12386 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12386
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12386 ≤ (1.036264300872 : ℝ) := by
  have hr : (111.292407647601 : ℝ) ≤ √(12386 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.292407647601 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12386 12386 (11 / 1000) ≤
    (0.008588969746 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12386) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.292407647601 : ℝ) ≤ √(12386 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12386)
  have hdiv : K / √(12386 : ℝ) ≤ K / 111.292407647601 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.292407647601 ≤ (0.008588969746 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12386.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12386 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12386 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12386 := gPlus_lower 12386
end BstLean.Part269.N12386

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12386
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036264300871 : ℝ) ≤ wn 12386 := by
  have hn : √(12386 : ℝ) ≤ 111.292407647602 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12386 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.292407647602 ≤ 2 / √(12386 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258379821 : ℝ) ≤ rhoBar 12386 BstLean.Part154.csC ∧
    rhoBar 12386 BstLean.Part154.csC ≤ 0.000258380221 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036264300871 : ℝ) / (1.295212 * 12386) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036264300872 : ℝ) / (1.29521 * 12386) := by gcongr
      _ ≤ (0.000258380221 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12386 BstLean.Part154.csC) ≤ 0.001033587645 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12386 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12386 BstLean.Part154.csC) (piBar (rhoBar 12386 BstLean.Part154.csC)) ≤ 0.000197352793 ∧
    cc1 (rhoBar 12386 BstLean.Part154.csC) (piBar (rhoBar 12386 BstLean.Part154.csC)) ≤ 0.000125576844 ∧
    cc2 (rhoBar 12386 BstLean.Part154.csC) ≤ 0.000072898261 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12386 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12386 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12386 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12386 BstLean.Part154.csC * nuR (rhoBar 12386 BstLean.Part154.csC)) ≤ 0.000516777132 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258380221 : ℝ) * 0.001033587645 := by gcongr
      _ ≤ (0.000516777132 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12386 BstLean.Part154.csC) * nuR (rhoBar 12386 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001033587645 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12386 BstLean.Part154.csC) * rhoBar 12386 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258380221 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258380221 / 2 + 0.399 * 0.001033587645 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197352793 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516777132 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125576844 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258380221 / 1.414213562 := by gcongr
      _ ≤ (0.000072898261 : ℝ) := by norm_num

end BstLean.Part269.N12386

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12386
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12386 BstLean.Part154.csC) (piBar (rhoBar 12386 BstLean.Part154.csC)) ≤ 1.68198E-7 := by
  have hr0 : 0 ≤ rhoBar 12386 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12386 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12386 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12386 BstLean.Part154.csC) (piBar (rhoBar 12386 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12386 BstLean.Part154.csC) (piBar (rhoBar 12386 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12386 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197352793 : ℝ) ^ 2 + 0.000125576844 ^ 2 + 3 * 0.000072898261 ^ 2 +
        2 * 0.797885 * 0.000197352793 * 0.000125576844 + 2 * 0.000197352793 * 0.000072898261 +
        4 * 0.797885 * 0.000125576844 * 0.000072898261 := by gcongr
    _ ≤ (1.68198E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12386 BstLean.Part154.csC Θ ≤ 0.002698315716 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12386 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12386 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12386 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12386 BstLean.Part154.csC) (piBar (rhoBar 12386 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12386 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036264300872 * 1.68198E-7 / (0.000258379821 : ℝ) := by gcongr
    _ ≤ 0.002698315716 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12386 BstLean.Part154.csC Θ ≤ 0.002995245300 + 0.000681820425 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12386 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12386 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12386 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036264300872 : ℝ) * ((2 * Θ * 0.000258380221 +
        (6863 / 10000) * 0.000258380221 * 12386 * 0.001033587645) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002995245300 + 0.000681820425 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12386 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12386 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12386 0.011 Θ ∧ gammaRatio 12386 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12386 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036264300872 : ℝ) * 0.525 / ((1 - 0.011) * 12386) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12386 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12386 0.011 Θ) :=
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
    badAllowance 12386 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12386 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12386 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12386 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12386 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12386 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12386 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12386 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12386 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12386 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12386 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036264300872 : ℝ) * 12386 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12386 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004095245300 + 0.003380136141 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12386

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12386
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12386 BstLean.Part154.csC) (piBar (rhoBar 12386 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12386 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12386 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12386 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12386 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12386 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12386 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12386 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12386 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12386 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12386 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12386 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12386 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12386 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12386 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053152678274 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12386) ≤ 0.010730629396 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12386 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036264300872)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010730629396 + 2 * 0.737676 / 12386) := by gcongr
    _ ≤ (0.053152678274 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12386 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12386

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12386
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489008291 : ℝ) ≤ plow 12386 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12386) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053376416775)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416615751) : eMP 12386 0.011 xi bn ≤ 0.001219189260 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12386 : ℝ) * (1 - 0.011))) ≤ 0.000602750126 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001416615751 / (12386 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602750126 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602750126 : ℝ) + 3.141593 * 0.053376416775 / (12386 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001219189260 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053376416775)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416615751) : PiBarMP 12386 12 0.011 xi bn ≤ 0.163304974893 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12386 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037637956255 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.678606785593 : ℝ) ≤ √((12386 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.292407647601 : ℝ) ≤ √(12386 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12386) ≤ 0.125187409971 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037637956255 + 0.053376416775 * 1.772454 / (2 * (110.678606785593 : ℝ))) * (1 + 0.001219189260) +
        8 / (12386 * 111.292407647601) + 0.125187409971 := by gcongr
    _ ≤ (0.163304974893 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053376416775)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416615751) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284186045507) :
    parallelOracle 12386 0.011 xi bn cd ≤ 0.164324327506 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12386 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12386 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489008291 : ℝ) ≤ plow 12386 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.292407647601 : ℝ) ≤ √(12386 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284186045507 : ℝ) / (2 * 0.560489008291 * 111.292407647601)) * 0.163304974893 +
        0.284186045507 ^ 2 / (2 * 0.560489008291 * 111.292407647601) := by gcongr
    _ ≤ (0.164324327506 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053376416775) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416615751)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284186045507) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12386 12386 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489008291 : ℝ) ≤ plow 12386 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.292407647601 : ℝ) ≤ √(12386 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12386 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12386 Θ 1.22 ≤ 0.011915462412 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.292407647601 := by gcongr <;> linarith
      _ ≤ (0.011915462412 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12386 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12386 12386 0.011 ≤ 0.008588969746 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12386 12386 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12386 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12386 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12386 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12386 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164324327506 + 0.011915462412 + (0.008588969746 : ℝ) *
        (1 + 2 * (0.284186045507 + 0.011915462412) / (0.560489008291 * 111.292407647601))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12386]

end BstLean.Part269.N12386

/-! The original eight local profiles supply actual 12386 moment certificates. -/
namespace BstLean.Part269.N12386
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12386 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12386 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12386 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053376416775 ∧
    0 ≤ bN 12386 BstLean.Part154.csC (groupTheta g) ∧ bN 12386 BstLean.Part154.csC (groupTheta g) ≤ 0.001416615751 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12386 12386 0.011
      (momentAllowance 12386 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12386 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12386 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12386 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12386 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12386 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231033367233 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12386 0.011
      (momentAllowance 12386 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12386 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12386
/-! The actual computed-centre upper energy formula at 12386. -/
namespace BstLean.Part269.N12386
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12386

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12386
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12386)
open BstLean.Part268 (cell12386)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086465699599
  | 2 => 0.087427798195
  | 3 => 0.088391082691
  | 4 => 0.089357655075
  | 5 => 0.090330032133
  | 6 => 0.091311203616
  | 7 => 0.092304695270
  | 8 => 0.093314636665
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12386 12386 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12386 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12386

/-! Actual upper energy certificates on all 43 source endpoints at 12386. -/
namespace BstLean.Part269.N12386
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12386)
open BstLean.Part268 (cell12386)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12386 (gMinus 12386) (1 - (cell12386 i).lower) ≤ 1 ∧
    energyUpper 12386 (gMinus 12386) (BstLean.Part211.gPlus 12386)
      (finiteEnergy 12386 12386 0.011) (1 - (cell12386 i).lower) ≤
      (cell12386 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨10,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨11,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨12,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨13,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨14,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨15,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨16,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨17,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨18,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨19,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨20,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨21,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨22,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨23,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨24,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨25,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨26,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨27,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨28,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨29,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨30,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨31,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨32,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨33,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨34,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨35,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨36,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨37,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨38,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨39,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨40,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨41,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨42,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨43,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨44,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨45,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨46,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨47,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨48,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨49,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨50,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨51,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12386) (by norm_num)
        (q := 1 - (cell12386 ⟨52,by decide⟩).lower)
        (by norm_num [cell12386]) (by norm_num [cell12386])
      exact ⟨E.1,E.2.trans (by norm_num [cell12386])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12386

/-! Source-cell containment and simple scalar guards at 12386. -/
namespace BstLean.Part269.N12386
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12386)
open BstLean.Part268 (cell12386)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12386 ⟨10,by decide⟩).lower ∧ (cell12386 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12386 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12386 ⟨11,by decide⟩).lower ∧ (cell12386 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12386 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12386 ⟨12,by decide⟩).lower ∧ (cell12386 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12386 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12386 ⟨13,by decide⟩).lower ∧ (cell12386 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12386 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12386 ⟨14,by decide⟩).lower ∧ (cell12386 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12386 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12386 ⟨15,by decide⟩).lower ∧ (cell12386 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12386 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12386 ⟨16,by decide⟩).lower ∧ (cell12386 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12386 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12386 ⟨17,by decide⟩).lower ∧ (cell12386 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12386 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12386 ⟨18,by decide⟩).lower ∧ (cell12386 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12386 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12386 ⟨19,by decide⟩).lower ∧ (cell12386 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12386 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12386 ⟨20,by decide⟩).lower ∧ (cell12386 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12386 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12386 ⟨21,by decide⟩).lower ∧ (cell12386 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12386 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12386 ⟨22,by decide⟩).lower ∧ (cell12386 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12386 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12386 ⟨23,by decide⟩).lower ∧ (cell12386 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12386 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12386 ⟨24,by decide⟩).lower ∧ (cell12386 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12386 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12386 ⟨25,by decide⟩).lower ∧ (cell12386 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12386 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12386 ⟨26,by decide⟩).lower ∧ (cell12386 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12386 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12386 ⟨27,by decide⟩).lower ∧ (cell12386 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12386 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12386 ⟨28,by decide⟩).lower ∧ (cell12386 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12386 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12386 ⟨29,by decide⟩).lower ∧ (cell12386 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12386 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12386 ⟨30,by decide⟩).lower ∧ (cell12386 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12386 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12386 ⟨31,by decide⟩).lower ∧ (cell12386 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12386 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12386 ⟨32,by decide⟩).lower ∧ (cell12386 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12386 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12386 ⟨33,by decide⟩).lower ∧ (cell12386 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12386 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12386 ⟨34,by decide⟩).lower ∧ (cell12386 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12386 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12386 ⟨35,by decide⟩).lower ∧ (cell12386 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12386 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12386 ⟨36,by decide⟩).lower ∧ (cell12386 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12386 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12386 ⟨37,by decide⟩).lower ∧ (cell12386 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12386 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12386 ⟨38,by decide⟩).lower ∧ (cell12386 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12386 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12386 ⟨39,by decide⟩).lower ∧ (cell12386 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12386 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12386 ⟨40,by decide⟩).lower ∧ (cell12386 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12386 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12386 ⟨41,by decide⟩).lower ∧ (cell12386 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12386 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12386 ⟨42,by decide⟩).lower ∧ (cell12386 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12386 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12386 ⟨43,by decide⟩).lower ∧ (cell12386 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12386 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12386 ⟨44,by decide⟩).lower ∧ (cell12386 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12386 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12386 ⟨45,by decide⟩).lower ∧ (cell12386 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12386 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12386 ⟨46,by decide⟩).lower ∧ (cell12386 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12386 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12386 ⟨47,by decide⟩).lower ∧ (cell12386 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12386 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12386 ⟨48,by decide⟩).lower ∧ (cell12386 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12386 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12386 ⟨49,by decide⟩).lower ∧ (cell12386 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12386 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12386 ⟨50,by decide⟩).lower ∧ (cell12386 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12386 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12386 ⟨51,by decide⟩).lower ∧ (cell12386 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12386 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12386 ⟨52,by decide⟩).lower ∧ (cell12386 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12386 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12386 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12386 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12386,cell12386,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12386 i).lower ∧
    (cell12386 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12386 i).upper ≤ (0.532 : ℝ) ∧
    (cell12386 i).centre ≤ (0.1 : ℝ) ∧ (cell12386 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12386 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12386 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12386

/-! The local source numeric instances at 12386 have no network premises. -/
namespace BstLean.Part269.N12386
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12386)
open BstLean.Part268 (cell12386)

noncomputable def sourceNumerics12386 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12386 (cell12386 i)
      scalarRow12386.M scalarRow12386.H scalarRow12386.xi := by
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
    energy_allowance := scalarRow12386.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12386]
    centre_nonneg := (scalarRow12386.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12386])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12386
/-! Actual 12387 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12387
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12387 ≤ (1.036262824002 : ℝ) := by
  have hr : (111.296900226376 : ℝ) ≤ √(12387 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.296900226376 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12387 12387 (11 / 1000) ≤
    (0.008588623044 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12387) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.296900226376 : ℝ) ≤ √(12387 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12387)
  have hdiv : K / √(12387 : ℝ) ≤ K / 111.296900226376 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.296900226376 ≤ (0.008588623044 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12387.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12387 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12387 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12387 := gPlus_lower 12387
end BstLean.Part269.N12387

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12387
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036262824001 : ℝ) ≤ wn 12387 := by
  have hn : √(12387 : ℝ) ≤ 111.296900226377 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12387 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.296900226377 ≤ 2 / √(12387 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000258358593 : ℝ) ≤ rhoBar 12387 BstLean.Part154.csC ∧
    rhoBar 12387 BstLean.Part154.csC ≤ 0.000258358993 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036262824001 : ℝ) / (1.295212 * 12387) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036262824002 : ℝ) / (1.29521 * 12387) := by gcongr
      _ ≤ (0.000258358993 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12387 BstLean.Part154.csC) ≤ 0.001033502722 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12387 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12387 BstLean.Part154.csC) (piBar (rhoBar 12387 BstLean.Part154.csC)) ≤ 0.000197336578 ∧
    cc1 (rhoBar 12387 BstLean.Part154.csC) (piBar (rhoBar 12387 BstLean.Part154.csC)) ≤ 0.000125566526 ∧
    cc2 (rhoBar 12387 BstLean.Part154.csC) ≤ 0.000072892271 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12387 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12387 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12387 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12387 BstLean.Part154.csC * nuR (rhoBar 12387 BstLean.Part154.csC)) ≤ 0.000516734674 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000258358993 : ℝ) * 0.001033502722 := by gcongr
      _ ≤ (0.000516734674 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12387 BstLean.Part154.csC) * nuR (rhoBar 12387 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001033502722 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12387 BstLean.Part154.csC) * rhoBar 12387 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000258358993 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000258358993 / 2 + 0.399 * 0.001033502722 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197336578 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000516734674 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125566526 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000258358993 / 1.414213562 := by gcongr
      _ ≤ (0.000072892271 : ℝ) := by norm_num

end BstLean.Part269.N12387

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12387
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12387 BstLean.Part154.csC) (piBar (rhoBar 12387 BstLean.Part154.csC)) ≤ 1.68171E-7 := by
  have hr0 : 0 ≤ rhoBar 12387 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12387 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12387 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12387 BstLean.Part154.csC) (piBar (rhoBar 12387 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12387 BstLean.Part154.csC) (piBar (rhoBar 12387 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12387 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197336578 : ℝ) ^ 2 + 0.000125566526 ^ 2 + 3 * 0.000072892271 ^ 2 +
        2 * 0.797885 * 0.000197336578 * 0.000125566526 + 2 * 0.000197336578 * 0.000072892271 +
        4 * 0.797885 * 0.000125566526 * 0.000072892271 := by gcongr
    _ ≤ (1.68171E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12387 BstLean.Part154.csC Θ ≤ 0.002698100394 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12387 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12387 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12387 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12387 BstLean.Part154.csC) (piBar (rhoBar 12387 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12387 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036262824002 * 1.68171E-7 / (0.000258358593 : ℝ) := by gcongr
    _ ≤ 0.002698100394 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12387 BstLean.Part154.csC Θ ≤ 0.002994990654 + 0.000681763437 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12387 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12387 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12387 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036262824002 : ℝ) * ((2 * Θ * 0.000258358993 +
        (6863 / 10000) * 0.000258358993 * 12387 * 0.001033502722) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002994990654 + 0.000681763437 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12387 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12387 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12387 0.011 Θ ∧ gammaRatio 12387 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12387 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036262824002 : ℝ) * 0.525 / ((1 - 0.011) * 12387) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12387 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12387 0.011 Θ) :=
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
    badAllowance 12387 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12387 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12387 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12387 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12387 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12387 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12387 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12387 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12387 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12387 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12387 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036262824002 : ℝ) * 12387 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12387 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004094990654 + 0.003379863831 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12387

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12387
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12387 BstLean.Part154.csC) (piBar (rhoBar 12387 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12387 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12387 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12387 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12387 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12387 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12387 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12387 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12387 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12387 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12387 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12387 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12387 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12387 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12387 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053150509177 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12387) ≤ 0.010730196247 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12387 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036262824002)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010730196247 + 2 * 0.737676 / 12387) := by gcongr
    _ ≤ (0.053150509177 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12387 12 ≤ 0.0015 := by
  exact BstLean.Part269.S1.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12387

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12387
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560489055832 : ℝ) ≤ plow 12387 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12387) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053376019166)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416502707) : eMP 12387 0.011 xi bn ≤ 0.001219091295 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12387 : ℝ) * (1 - 0.011))) ≤ 0.000602701747 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001416502707 / (12387 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000602701747 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000602701747 : ℝ) + 3.141593 * 0.053376019166 / (12387 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001219091295 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053376019166)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416502707) : PiBarMP 12387 12 0.011 xi bn ≤ 0.163298393131 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12387 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037636454496 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.683074586858 : ℝ) ≤ √((12387 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.296900226376 : ℝ) ≤ √(12387 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12387) ≤ 0.125182356692 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037636454496 + 0.053376019166 * 1.772454 / (2 * (110.683074586858 : ℝ))) * (1 + 0.001219091295) +
        8 / (12387 * 111.296900226376) + 0.125182356692 := by gcongr
    _ ≤ (0.163298393131 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053376019166)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416502707) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284183015908) :
    parallelOracle 12387 0.011 xi bn cd ≤ 0.164317671751 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12387 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12387 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560489055832 : ℝ) ≤ plow 12387 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.296900226376 : ℝ) ≤ √(12387 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284183015908 : ℝ) / (2 * 0.560489055832 * 111.296900226376)) * 0.163298393131 +
        0.284183015908 ^ 2 / (2 * 0.560489055832 * 111.296900226376) := by gcongr
    _ ≤ (0.164317671751 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053376019166) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001416502707)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284183015908) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12387 12387 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560489055832 : ℝ) ≤ plow 12387 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.296900226376 : ℝ) ≤ √(12387 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12387 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12387 Θ 1.22 ≤ 0.011914981436 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.296900226376 := by gcongr <;> linarith
      _ ≤ (0.011914981436 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12387 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12387 12387 0.011 ≤ 0.008588623044 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12387 12387 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12387 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12387 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12387 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12387 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164317671751 + 0.011914981436 + (0.008588623044 : ℝ) *
        (1 + 2 * (0.284183015908 + 0.011914981436) / (0.560489055832 * 111.296900226376))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12387]

end BstLean.Part269.N12387

/-! The original eight local profiles supply actual 12387 moment certificates. -/
namespace BstLean.Part269.N12387
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12387 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12387 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12387 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053376019166 ∧
    0 ≤ bN 12387 BstLean.Part154.csC (groupTheta g) ∧ bN 12387 BstLean.Part154.csC (groupTheta g) ≤ 0.001416502707 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12387 12387 0.011
      (momentAllowance 12387 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12387 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12387 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12387 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12387 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12387 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231032506731 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12387 0.011
      (momentAllowance 12387 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12387 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12387
/-! The actual computed-centre upper energy formula at 12387. -/
namespace BstLean.Part269.N12387
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12387

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12387
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12387)
open BstLean.Part268 (cell12387)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086462381429
  | 2 => 0.087424409215
  | 3 => 0.088387611052
  | 4 => 0.089354086328
  | 5 => 0.090326348789
  | 6 => 0.091307384660
  | 7 => 0.092300715623
  | 8 => 0.093310466587
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12387 12387 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12387 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12387

/-! Actual upper energy certificates on all 43 source endpoints at 12387. -/
namespace BstLean.Part269.N12387
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12387)
open BstLean.Part268 (cell12387)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12387 (gMinus 12387) (1 - (cell12387 i).lower) ≤ 1 ∧
    energyUpper 12387 (gMinus 12387) (BstLean.Part211.gPlus 12387)
      (finiteEnergy 12387 12387 0.011) (1 - (cell12387 i).lower) ≤
      (cell12387 i).energy := by
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
      have E := BstLean.Part269.S1.uniformEnergy10 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨10,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy11 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨11,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy12 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨12,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy13 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨13,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy14 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨14,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy15 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨15,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy16 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨16,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy17 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨17,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy18 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨18,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy19 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨19,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy20 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨20,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy21 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨21,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy22 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨22,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy23 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨23,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy24 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨24,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy25 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨25,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy26 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨26,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy27 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨27,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy28 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨28,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy29 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨29,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy30 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨30,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy31 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨31,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy32 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨32,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy33 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨33,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy34 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨34,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy35 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨35,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy36 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨36,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy37 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨37,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy38 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨38,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy39 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨39,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy40 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨40,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy41 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨41,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy42 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨42,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy43 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨43,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy44 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨44,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy45 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨45,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy46 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨46,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy47 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨47,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy48 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨48,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy49 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨49,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy50 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨50,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy51 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨51,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S1.uniformEnergy52 (n := 12387) (by norm_num)
        (q := 1 - (cell12387 ⟨52,by decide⟩).lower)
        (by norm_num [cell12387]) (by norm_num [cell12387])
      exact ⟨E.1,E.2.trans (by norm_num [cell12387])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12387

/-! Source-cell containment and simple scalar guards at 12387. -/
namespace BstLean.Part269.N12387
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12387)
open BstLean.Part268 (cell12387)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12387 ⟨10,by decide⟩).lower ∧ (cell12387 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12387 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12387 ⟨11,by decide⟩).lower ∧ (cell12387 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12387 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12387 ⟨12,by decide⟩).lower ∧ (cell12387 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12387 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12387 ⟨13,by decide⟩).lower ∧ (cell12387 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12387 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12387 ⟨14,by decide⟩).lower ∧ (cell12387 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12387 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12387 ⟨15,by decide⟩).lower ∧ (cell12387 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12387 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12387 ⟨16,by decide⟩).lower ∧ (cell12387 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12387 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12387 ⟨17,by decide⟩).lower ∧ (cell12387 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12387 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12387 ⟨18,by decide⟩).lower ∧ (cell12387 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12387 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12387 ⟨19,by decide⟩).lower ∧ (cell12387 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12387 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12387 ⟨20,by decide⟩).lower ∧ (cell12387 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12387 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12387 ⟨21,by decide⟩).lower ∧ (cell12387 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12387 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12387 ⟨22,by decide⟩).lower ∧ (cell12387 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12387 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12387 ⟨23,by decide⟩).lower ∧ (cell12387 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12387 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12387 ⟨24,by decide⟩).lower ∧ (cell12387 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12387 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12387 ⟨25,by decide⟩).lower ∧ (cell12387 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12387 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12387 ⟨26,by decide⟩).lower ∧ (cell12387 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12387 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12387 ⟨27,by decide⟩).lower ∧ (cell12387 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12387 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12387 ⟨28,by decide⟩).lower ∧ (cell12387 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12387 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12387 ⟨29,by decide⟩).lower ∧ (cell12387 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12387 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12387 ⟨30,by decide⟩).lower ∧ (cell12387 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12387 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12387 ⟨31,by decide⟩).lower ∧ (cell12387 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12387 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12387 ⟨32,by decide⟩).lower ∧ (cell12387 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12387 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12387 ⟨33,by decide⟩).lower ∧ (cell12387 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12387 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12387 ⟨34,by decide⟩).lower ∧ (cell12387 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12387 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12387 ⟨35,by decide⟩).lower ∧ (cell12387 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12387 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12387 ⟨36,by decide⟩).lower ∧ (cell12387 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12387 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12387 ⟨37,by decide⟩).lower ∧ (cell12387 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12387 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12387 ⟨38,by decide⟩).lower ∧ (cell12387 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12387 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12387 ⟨39,by decide⟩).lower ∧ (cell12387 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12387 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12387 ⟨40,by decide⟩).lower ∧ (cell12387 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12387 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12387 ⟨41,by decide⟩).lower ∧ (cell12387 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12387 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12387 ⟨42,by decide⟩).lower ∧ (cell12387 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12387 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12387 ⟨43,by decide⟩).lower ∧ (cell12387 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12387 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12387 ⟨44,by decide⟩).lower ∧ (cell12387 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12387 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12387 ⟨45,by decide⟩).lower ∧ (cell12387 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12387 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12387 ⟨46,by decide⟩).lower ∧ (cell12387 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12387 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12387 ⟨47,by decide⟩).lower ∧ (cell12387 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12387 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12387 ⟨48,by decide⟩).lower ∧ (cell12387 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12387 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12387 ⟨49,by decide⟩).lower ∧ (cell12387 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12387 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12387 ⟨50,by decide⟩).lower ∧ (cell12387 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12387 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12387 ⟨51,by decide⟩).lower ∧ (cell12387 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12387 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12387 ⟨52,by decide⟩).lower ∧ (cell12387 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12387 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12387 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12387 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12387,cell12387,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12387 i).lower ∧
    (cell12387 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12387 i).upper ≤ (0.532 : ℝ) ∧
    (cell12387 i).centre ≤ (0.1 : ℝ) ∧ (cell12387 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12387 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12387 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12387

/-! The local source numeric instances at 12387 have no network premises. -/
namespace BstLean.Part269.N12387
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12387)
open BstLean.Part268 (cell12387)

noncomputable def sourceNumerics12387 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12387 (cell12387 i)
      scalarRow12387.M scalarRow12387.H scalarRow12387.xi := by
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
    energy_allowance := scalarRow12387.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12387]
    centre_nonneg := (scalarRow12387.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D1.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12387])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12387