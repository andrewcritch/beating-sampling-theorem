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
import BstLean.Part269Direction21
import BstLean.Part269Shared21
import BstLean.Part269Finite
import BstLean.Part269Rows21
import BstLean.Part269Source
/-! Actual 12888 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12888
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12888 ≤ (1.035544794405 : ℝ) := by
  have hr : (113.525327570547 : ℝ) ≤ √(12888 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.525327570547 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12888 12888 (11 / 1000) ≤
    (0.008420032745 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12888) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.525327570547 : ℝ) ≤ √(12888 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12888)
  have hdiv : K / √(12888 : ℝ) ≤ K / 113.525327570547 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.525327570547 ≤ (0.008420032745 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12888.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12888 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12888 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12888 := gPlus_lower 12888
end BstLean.Part269.N12888

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12888
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035544794404 : ℝ) ≤ wn 12888 := by
  have hn : √(12888 : ℝ) ≤ 113.525327570548 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12888 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.525327570548 ≤ 2 / √(12888 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248143266 : ℝ) ≤ rhoBar 12888 BstLean.Part154.csC ∧
    rhoBar 12888 BstLean.Part154.csC ≤ 0.000248143650 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035544794404 : ℝ) / (1.295212 * 12888) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035544794405 : ℝ) / (1.29521 * 12888) := by gcongr
      _ ≤ (0.000248143650 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12888 BstLean.Part154.csC) ≤ 0.000992636176 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12888 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12888 BstLean.Part154.csC) (piBar (rhoBar 12888 BstLean.Part154.csC)) ≤ 0.000189533663 ∧
    cc1 (rhoBar 12888 BstLean.Part154.csC) (piBar (rhoBar 12888 BstLean.Part154.csC)) ≤ 0.000120601555 ∧
    cc2 (rhoBar 12888 BstLean.Part154.csC) ≤ 0.000070010160 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12888 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12888 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12888 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12888 BstLean.Part154.csC * nuR (rhoBar 12888 BstLean.Part154.csC)) ≤ 0.000496302694 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248143650 : ℝ) * 0.000992636176 := by gcongr
      _ ≤ (0.000496302694 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12888 BstLean.Part154.csC) * nuR (rhoBar 12888 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000992636176 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12888 BstLean.Part154.csC) * rhoBar 12888 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248143650 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248143650 / 2 + 0.399 * 0.000992636176 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189533663 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496302694 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120601555 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248143650 / 1.414213562 := by gcongr
      _ ≤ (0.000070010160 : ℝ) := by norm_num

end BstLean.Part269.N12888

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12888
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12888 BstLean.Part154.csC) (piBar (rhoBar 12888 BstLean.Part154.csC)) ≤ 1.55135E-7 := by
  have hr0 : 0 ≤ rhoBar 12888 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12888 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12888 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12888 BstLean.Part154.csC) (piBar (rhoBar 12888 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12888 BstLean.Part154.csC) (piBar (rhoBar 12888 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12888 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189533663 : ℝ) ^ 2 + 0.000120601555 ^ 2 + 3 * 0.000070010160 ^ 2 +
        2 * 0.797885 * 0.000189533663 * 0.000120601555 + 2 * 0.000189533663 * 0.000070010160 +
        4 * 0.797885 * 0.000120601555 * 0.000070010160 := by gcongr
    _ ≤ (1.55135E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12888 BstLean.Part154.csC Θ ≤ 0.002589620815 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12888 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12888 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12888 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12888 BstLean.Part154.csC) (piBar (rhoBar 12888 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12888 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035544794405 * 1.55135E-7 / (0.000248143266 : ℝ) := by gcongr
    _ ≤ 0.002589620815 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12888 BstLean.Part154.csC Θ ≤ 0.002872578397 + 0.000654353246 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12888 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12888 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12888 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035544794405 : ℝ) * ((2 * Θ * 0.000248143650 +
        (6863 / 10000) * 0.000248143650 * 12888 * 0.000992636176) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002872578397 + 0.000654353246 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12888 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12888 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12888 0.011 Θ ∧ gammaRatio 12888 0.011 Θ ≤ 0.000085305370 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12888 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035544794405 : ℝ) * 0.525 / ((1 - 0.011) * 12888) := by gcongr
      _ ≤ (0.000085305370 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12888 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12888 0.011 Θ) :=
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
    badAllowance 12888 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12888 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12888 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12888 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12888 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12888 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12888 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12888 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12888 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12888 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12888 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035544794405 : ℝ) * 12888 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12888 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003335614452 + 0.003243974061 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12888

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12888
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12888 BstLean.Part154.csC) (piBar (rhoBar 12888 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12888 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12888 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12888 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12888 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12888 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12888 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12888 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12888 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12888 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12888 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12888 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12888 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12888 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12888 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052095970974 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12888) ≤ 0.010519569568 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12888 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035544794405)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010519569568 + 2 * 0.737676 / 12888) := by gcongr
    _ ≤ (0.052095970974 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12888 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12888

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12888
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511946190 : ℝ) ≤ plow 12888 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12888) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052545300835)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359550928) : eMP 12888 0.011 xi bn ≤ 0.001170692957 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12888 : ℝ) * (1 - 0.011))) ≤ 0.000578870998 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001359550928 / (12888 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578870998 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578870998 : ℝ) + 3.141593 * 0.052545300835 / (12888 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001170692957 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052545300835)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359550928) : PiBarMP 12888 12 0.011 xi bn ≤ 0.160058780650 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12888 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036872088740 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.899211689010 : ℝ) ≤ √((12888 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.525327570547 : ℝ) ≤ √(12888 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12888) ≤ 0.122725109550 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036872088740 + 0.052545300835 * 1.772454 / (2 * (112.899211689010 : ℝ))) * (1 + 0.001170692957) +
        8 / (12888 * 113.525327570547) + 0.122725109550 := by gcongr
    _ ≤ (0.160058780650 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052545300835)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359550928) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281323588933) :
    parallelOracle 12888 0.011 xi bn cd ≤ 0.161034474346 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12888 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12888 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511946190 : ℝ) ≤ plow 12888 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.525327570547 : ℝ) ≤ √(12888 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281323588933 : ℝ) / (2 * 0.560511946190 * 113.525327570547)) * 0.160058780650 +
        0.281323588933 ^ 2 / (2 * 0.560511946190 * 113.525327570547) := by gcongr
    _ ≤ (0.161034474346 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052545300835) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359550928)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281323588933) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12888 12888 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511946190 : ℝ) ≤ plow 12888 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.525327570547 : ℝ) ≤ √(12888 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12888 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12888 Θ 1.22 ≤ 0.011681098205 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.525327570547 := by gcongr <;> linarith
      _ ≤ (0.011681098205 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12888 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12888 12888 0.011 ≤ 0.008420032745 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12888 12888 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12888 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12888 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12888 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12888 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161034474346 + 0.011681098205 + (0.008420032745 : ℝ) *
        (1 + 2 * (0.281323588933 + 0.011681098205) / (0.560511946190 * 113.525327570547))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12888]

end BstLean.Part269.N12888

/-! The original eight local profiles supply actual 12888 moment certificates. -/
namespace BstLean.Part269.N12888
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12888 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12888 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12888 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052545300835 ∧
    0 ≤ bN 12888 BstLean.Part154.csC (groupTheta g) ∧ bN 12888 BstLean.Part154.csC (groupTheta g) ≤ 0.001359550928 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12888 12888 0.011
      (momentAllowance 12888 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12888 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12888 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12888 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12888 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12888 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229227617959 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12888 0.011
      (momentAllowance 12888 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12888 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12888
/-! The actual computed-centre upper energy formula at 12888. -/
namespace BstLean.Part269.N12888
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12888

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12888
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12888)
open BstLean.Part268 (cell12888)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084960002559
  | 2 => 0.085893405238
  | 3 => 0.086823648880
  | 4 => 0.087751848043
  | 5 => 0.088679360124
  | 6 => 0.089607822605
  | 7 => 0.090539194017
  | 8 => 0.091475798714
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12888 12888 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12888 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003338665865 + 0.003247348463 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S21.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12888

/-! Actual upper energy certificates on all 43 source endpoints at 12888. -/
namespace BstLean.Part269.N12888
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12888)
open BstLean.Part268 (cell12888)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12888 (gMinus 12888) (1 - (cell12888 i).lower) ≤ 1 ∧
    energyUpper 12888 (gMinus 12888) (BstLean.Part211.gPlus 12888)
      (finiteEnergy 12888 12888 0.011) (1 - (cell12888 i).lower) ≤
      (cell12888 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨10,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨11,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨12,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨13,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨14,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨15,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨16,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨17,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨18,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨19,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨20,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨21,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨22,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨23,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨24,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨25,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨26,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨27,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨28,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨29,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨30,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨31,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨32,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨33,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨34,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨35,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨36,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨37,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨38,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨39,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨40,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨41,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨42,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨43,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨44,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨45,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨46,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨47,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨48,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨49,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨50,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨51,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12888) (by norm_num)
        (q := 1 - (cell12888 ⟨52,by decide⟩).lower)
        (by norm_num [cell12888]) (by norm_num [cell12888])
      exact ⟨E.1,E.2.trans (by norm_num [cell12888])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12888

/-! Source-cell containment and simple scalar guards at 12888. -/
namespace BstLean.Part269.N12888
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12888)
open BstLean.Part268 (cell12888)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12888 ⟨10,by decide⟩).lower ∧ (cell12888 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12888 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12888 ⟨11,by decide⟩).lower ∧ (cell12888 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12888 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12888 ⟨12,by decide⟩).lower ∧ (cell12888 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12888 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12888 ⟨13,by decide⟩).lower ∧ (cell12888 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12888 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12888 ⟨14,by decide⟩).lower ∧ (cell12888 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12888 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12888 ⟨15,by decide⟩).lower ∧ (cell12888 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12888 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12888 ⟨16,by decide⟩).lower ∧ (cell12888 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12888 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12888 ⟨17,by decide⟩).lower ∧ (cell12888 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12888 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12888 ⟨18,by decide⟩).lower ∧ (cell12888 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12888 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12888 ⟨19,by decide⟩).lower ∧ (cell12888 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12888 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12888 ⟨20,by decide⟩).lower ∧ (cell12888 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12888 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12888 ⟨21,by decide⟩).lower ∧ (cell12888 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12888 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12888 ⟨22,by decide⟩).lower ∧ (cell12888 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12888 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12888 ⟨23,by decide⟩).lower ∧ (cell12888 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12888 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12888 ⟨24,by decide⟩).lower ∧ (cell12888 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12888 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12888 ⟨25,by decide⟩).lower ∧ (cell12888 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12888 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12888 ⟨26,by decide⟩).lower ∧ (cell12888 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12888 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12888 ⟨27,by decide⟩).lower ∧ (cell12888 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12888 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12888 ⟨28,by decide⟩).lower ∧ (cell12888 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12888 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12888 ⟨29,by decide⟩).lower ∧ (cell12888 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12888 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12888 ⟨30,by decide⟩).lower ∧ (cell12888 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12888 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12888 ⟨31,by decide⟩).lower ∧ (cell12888 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12888 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12888 ⟨32,by decide⟩).lower ∧ (cell12888 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12888 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12888 ⟨33,by decide⟩).lower ∧ (cell12888 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12888 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12888 ⟨34,by decide⟩).lower ∧ (cell12888 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12888 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12888 ⟨35,by decide⟩).lower ∧ (cell12888 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12888 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12888 ⟨36,by decide⟩).lower ∧ (cell12888 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12888 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12888 ⟨37,by decide⟩).lower ∧ (cell12888 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12888 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12888 ⟨38,by decide⟩).lower ∧ (cell12888 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12888 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12888 ⟨39,by decide⟩).lower ∧ (cell12888 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12888 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12888 ⟨40,by decide⟩).lower ∧ (cell12888 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12888 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12888 ⟨41,by decide⟩).lower ∧ (cell12888 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12888 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12888 ⟨42,by decide⟩).lower ∧ (cell12888 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12888 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12888 ⟨43,by decide⟩).lower ∧ (cell12888 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12888 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12888 ⟨44,by decide⟩).lower ∧ (cell12888 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12888 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12888 ⟨45,by decide⟩).lower ∧ (cell12888 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12888 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12888 ⟨46,by decide⟩).lower ∧ (cell12888 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12888 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12888 ⟨47,by decide⟩).lower ∧ (cell12888 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12888 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12888 ⟨48,by decide⟩).lower ∧ (cell12888 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12888 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12888 ⟨49,by decide⟩).lower ∧ (cell12888 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12888 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12888 ⟨50,by decide⟩).lower ∧ (cell12888 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12888 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12888 ⟨51,by decide⟩).lower ∧ (cell12888 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12888 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12888 ⟨52,by decide⟩).lower ∧ (cell12888 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12888 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12888 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12888 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12888,cell12888,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12888 i).lower ∧
    (cell12888 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12888 i).upper ≤ (0.532 : ℝ) ∧
    (cell12888 i).centre ≤ (0.1 : ℝ) ∧ (cell12888 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12888 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12888 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12888

/-! The local source numeric instances at 12888 have no network premises. -/
namespace BstLean.Part269.N12888
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12888)
open BstLean.Part268 (cell12888)

noncomputable def sourceNumerics12888 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12888 (cell12888 i)
      scalarRow12888.M scalarRow12888.H scalarRow12888.xi := by
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
    energy_allowance := scalarRow12888.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12888]
    centre_nonneg := (scalarRow12888.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12888])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12888
/-! Actual 12889 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12889
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12889 ≤ (1.035543403457 : ℝ) := by
  have hr : (113.529731788637 : ℝ) ≤ √(12889 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.529731788637 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12889 12889 (11 / 1000) ≤
    (0.008419706100 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12889) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.529731788637 : ℝ) ≤ √(12889 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12889)
  have hdiv : K / √(12889 : ℝ) ≤ K / 113.529731788637 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.529731788637 ≤ (0.008419706100 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12889.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12889 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12889 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12889 := gPlus_lower 12889
end BstLean.Part269.N12889

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12889
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035543403456 : ℝ) ≤ wn 12889 := by
  have hn : √(12889 : ℝ) ≤ 113.529731788638 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12889 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.529731788638 ≤ 2 / √(12889 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248123680 : ℝ) ≤ rhoBar 12889 BstLean.Part154.csC ∧
    rhoBar 12889 BstLean.Part154.csC ≤ 0.000248124064 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035543403456 : ℝ) / (1.295212 * 12889) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035543403457 : ℝ) / (1.29521 * 12889) := by gcongr
      _ ≤ (0.000248124064 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12889 BstLean.Part154.csC) ≤ 0.000992557822 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12889 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12889 BstLean.Part154.csC) (piBar (rhoBar 12889 BstLean.Part154.csC)) ≤ 0.000189518702 ∧
    cc1 (rhoBar 12889 BstLean.Part154.csC) (piBar (rhoBar 12889 BstLean.Part154.csC)) ≤ 0.000120592036 ∧
    cc2 (rhoBar 12889 BstLean.Part154.csC) ≤ 0.000070004634 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12889 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12889 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12889 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12889 BstLean.Part154.csC * nuR (rhoBar 12889 BstLean.Part154.csC)) ≤ 0.000496263520 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248124064 : ℝ) * 0.000992557822 := by gcongr
      _ ≤ (0.000496263520 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12889 BstLean.Part154.csC) * nuR (rhoBar 12889 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000992557822 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12889 BstLean.Part154.csC) * rhoBar 12889 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248124064 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248124064 / 2 + 0.399 * 0.000992557822 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189518702 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496263520 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120592036 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248124064 / 1.414213562 := by gcongr
      _ ≤ (0.000070004634 : ℝ) := by norm_num

end BstLean.Part269.N12889

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12889
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12889 BstLean.Part154.csC) (piBar (rhoBar 12889 BstLean.Part154.csC)) ≤ 1.55110E-7 := by
  have hr0 : 0 ≤ rhoBar 12889 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12889 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12889 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12889 BstLean.Part154.csC) (piBar (rhoBar 12889 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12889 BstLean.Part154.csC) (piBar (rhoBar 12889 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12889 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189518702 : ℝ) ^ 2 + 0.000120592036 ^ 2 + 3 * 0.000070004634 ^ 2 +
        2 * 0.797885 * 0.000189518702 * 0.000120592036 + 2 * 0.000189518702 * 0.000070004634 +
        4 * 0.797885 * 0.000120592036 * 0.000070004634 := by gcongr
    _ ≤ (1.55110E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12889 BstLean.Part154.csC Θ ≤ 0.002589404403 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12889 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12889 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12889 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12889 BstLean.Part154.csC) (piBar (rhoBar 12889 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12889 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035543403457 * 1.55110E-7 / (0.000248123680 : ℝ) := by gcongr
    _ ≤ 0.002589404403 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12889 BstLean.Part154.csC Θ ≤ 0.002872343928 + 0.000654300719 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12889 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12889 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12889 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035543403457 : ℝ) * ((2 * Θ * 0.000248124064 +
        (6863 / 10000) * 0.000248124064 * 12889 * 0.000992557822) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002872343928 + 0.000654300719 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12889 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12889 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12889 0.011 Θ ∧ gammaRatio 12889 0.011 Θ ≤ 0.000085298637 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12889 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035543403457 : ℝ) * 0.525 / ((1 - 0.011) * 12889) := by gcongr
      _ ≤ (0.000085298637 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12889 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12889 0.011 Θ) :=
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
    badAllowance 12889 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12889 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12889 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12889 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12889 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12889 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12889 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12889 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12889 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12889 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12889 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035543403457 : ℝ) * 12889 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12889 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003335379983 + 0.003243705122 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12889

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12889
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12889 BstLean.Part154.csC) (piBar (rhoBar 12889 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12889 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12889 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12889 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12889 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12889 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12889 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12889 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12889 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12889 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12889 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12889 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12889 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12889 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12889 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052093928234 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12889) ≤ 0.010519161477 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12889 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035543403457)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010519161477 + 2 * 0.737676 / 12889) := by gcongr
    _ ≤ (0.052093928234 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12889 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12889

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12889
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511990100 : ℝ) ≤ plow 12889 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12889) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052544925173)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359437312) : eMP 12889 0.011 xi bn ≤ 0.001170598572 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12889 : ℝ) * (1 - 0.011))) ≤ 0.000578824354 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001359437312 / (12889 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578824354 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578824354 : ℝ) + 3.141593 * 0.052544925173 / (12889 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001170598572 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052544925173)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359437312) : PiBarMP 12889 12 0.011 xi bn ≤ 0.160052454070 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12889 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036870548030 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.903591616918 : ℝ) ≤ √((12889 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.529731788637 : ℝ) ≤ √(12889 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12889) ≤ 0.122720348611 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036870548030 + 0.052544925173 * 1.772454 / (2 * (112.903591616918 : ℝ))) * (1 + 0.001170598572) +
        8 / (12889 * 113.529731788637) + 0.122720348611 := by gcongr
    _ ≤ (0.160052454070 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052544925173)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359437312) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281320726783) :
    parallelOracle 12889 0.011 xi bn cd ≤ 0.161028079601 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12889 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12889 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511990100 : ℝ) ≤ plow 12889 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.529731788637 : ℝ) ≤ √(12889 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281320726783 : ℝ) / (2 * 0.560511990100 * 113.529731788637)) * 0.160052454070 +
        0.281320726783 ^ 2 / (2 * 0.560511990100 * 113.529731788637) := by gcongr
    _ ≤ (0.161028079601 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052544925173) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359437312)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281320726783) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12889 12889 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511990100 : ℝ) ≤ plow 12889 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.529731788637 : ℝ) ≤ √(12889 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12889 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12889 Θ 1.22 ≤ 0.011680645054 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.529731788637 := by gcongr <;> linarith
      _ ≤ (0.011680645054 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12889 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12889 12889 0.011 ≤ 0.008419706100 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12889 12889 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12889 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12889 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12889 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12889 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161028079601 + 0.011680645054 + (0.008419706100 : ℝ) *
        (1 + 2 * (0.281320726783 + 0.011680645054) / (0.560511990100 * 113.529731788637))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12889]

end BstLean.Part269.N12889

/-! The original eight local profiles supply actual 12889 moment certificates. -/
namespace BstLean.Part269.N12889
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12889 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12889 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12889 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052544925173 ∧
    0 ≤ bN 12889 BstLean.Part154.csC (groupTheta g) ∧ bN 12889 BstLean.Part154.csC (groupTheta g) ≤ 0.001359437312 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12889 12889 0.011
      (momentAllowance 12889 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12889 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12889 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12889 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12889 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12889 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229226798549 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12889 0.011
      (momentAllowance 12889 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12889 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12889
/-! The actual computed-centre upper energy formula at 12889. -/
namespace BstLean.Part269.N12889
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12889

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12889
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12889)
open BstLean.Part268 (cell12889)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084957272568
  | 2 => 0.085890629111
  | 3 => 0.086820820553
  | 4 => 0.087748960009
  | 5 => 0.088676403176
  | 6 => 0.089604785536
  | 7 => 0.090536063294
  | 8 => 0.091472558105
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12889 12889 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12889 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003338665865 + 0.003247348463 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S21.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12889

/-! Actual upper energy certificates on all 43 source endpoints at 12889. -/
namespace BstLean.Part269.N12889
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12889)
open BstLean.Part268 (cell12889)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12889 (gMinus 12889) (1 - (cell12889 i).lower) ≤ 1 ∧
    energyUpper 12889 (gMinus 12889) (BstLean.Part211.gPlus 12889)
      (finiteEnergy 12889 12889 0.011) (1 - (cell12889 i).lower) ≤
      (cell12889 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨10,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨11,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨12,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨13,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨14,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨15,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨16,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨17,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨18,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨19,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨20,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨21,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨22,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨23,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨24,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨25,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨26,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨27,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨28,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨29,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨30,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨31,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨32,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨33,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨34,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨35,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨36,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨37,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨38,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨39,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨40,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨41,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨42,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨43,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨44,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨45,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨46,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨47,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨48,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨49,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨50,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨51,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12889) (by norm_num)
        (q := 1 - (cell12889 ⟨52,by decide⟩).lower)
        (by norm_num [cell12889]) (by norm_num [cell12889])
      exact ⟨E.1,E.2.trans (by norm_num [cell12889])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12889

/-! Source-cell containment and simple scalar guards at 12889. -/
namespace BstLean.Part269.N12889
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12889)
open BstLean.Part268 (cell12889)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12889 ⟨10,by decide⟩).lower ∧ (cell12889 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12889 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12889 ⟨11,by decide⟩).lower ∧ (cell12889 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12889 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12889 ⟨12,by decide⟩).lower ∧ (cell12889 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12889 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12889 ⟨13,by decide⟩).lower ∧ (cell12889 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12889 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12889 ⟨14,by decide⟩).lower ∧ (cell12889 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12889 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12889 ⟨15,by decide⟩).lower ∧ (cell12889 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12889 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12889 ⟨16,by decide⟩).lower ∧ (cell12889 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12889 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12889 ⟨17,by decide⟩).lower ∧ (cell12889 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12889 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12889 ⟨18,by decide⟩).lower ∧ (cell12889 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12889 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12889 ⟨19,by decide⟩).lower ∧ (cell12889 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12889 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12889 ⟨20,by decide⟩).lower ∧ (cell12889 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12889 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12889 ⟨21,by decide⟩).lower ∧ (cell12889 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12889 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12889 ⟨22,by decide⟩).lower ∧ (cell12889 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12889 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12889 ⟨23,by decide⟩).lower ∧ (cell12889 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12889 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12889 ⟨24,by decide⟩).lower ∧ (cell12889 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12889 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12889 ⟨25,by decide⟩).lower ∧ (cell12889 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12889 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12889 ⟨26,by decide⟩).lower ∧ (cell12889 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12889 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12889 ⟨27,by decide⟩).lower ∧ (cell12889 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12889 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12889 ⟨28,by decide⟩).lower ∧ (cell12889 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12889 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12889 ⟨29,by decide⟩).lower ∧ (cell12889 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12889 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12889 ⟨30,by decide⟩).lower ∧ (cell12889 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12889 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12889 ⟨31,by decide⟩).lower ∧ (cell12889 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12889 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12889 ⟨32,by decide⟩).lower ∧ (cell12889 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12889 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12889 ⟨33,by decide⟩).lower ∧ (cell12889 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12889 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12889 ⟨34,by decide⟩).lower ∧ (cell12889 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12889 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12889 ⟨35,by decide⟩).lower ∧ (cell12889 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12889 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12889 ⟨36,by decide⟩).lower ∧ (cell12889 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12889 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12889 ⟨37,by decide⟩).lower ∧ (cell12889 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12889 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12889 ⟨38,by decide⟩).lower ∧ (cell12889 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12889 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12889 ⟨39,by decide⟩).lower ∧ (cell12889 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12889 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12889 ⟨40,by decide⟩).lower ∧ (cell12889 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12889 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12889 ⟨41,by decide⟩).lower ∧ (cell12889 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12889 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12889 ⟨42,by decide⟩).lower ∧ (cell12889 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12889 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12889 ⟨43,by decide⟩).lower ∧ (cell12889 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12889 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12889 ⟨44,by decide⟩).lower ∧ (cell12889 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12889 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12889 ⟨45,by decide⟩).lower ∧ (cell12889 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12889 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12889 ⟨46,by decide⟩).lower ∧ (cell12889 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12889 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12889 ⟨47,by decide⟩).lower ∧ (cell12889 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12889 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12889 ⟨48,by decide⟩).lower ∧ (cell12889 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12889 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12889 ⟨49,by decide⟩).lower ∧ (cell12889 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12889 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12889 ⟨50,by decide⟩).lower ∧ (cell12889 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12889 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12889 ⟨51,by decide⟩).lower ∧ (cell12889 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12889 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12889 ⟨52,by decide⟩).lower ∧ (cell12889 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12889 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12889 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12889 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12889,cell12889,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12889 i).lower ∧
    (cell12889 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12889 i).upper ≤ (0.532 : ℝ) ∧
    (cell12889 i).centre ≤ (0.1 : ℝ) ∧ (cell12889 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12889 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12889 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12889

/-! The local source numeric instances at 12889 have no network premises. -/
namespace BstLean.Part269.N12889
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12889)
open BstLean.Part268 (cell12889)

noncomputable def sourceNumerics12889 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12889 (cell12889 i)
      scalarRow12889.M scalarRow12889.H scalarRow12889.xi := by
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
    energy_allowance := scalarRow12889.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12889]
    centre_nonneg := (scalarRow12889.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12889])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12889
/-! Actual 12890 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12890
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12890 ≤ (1.035542012673 : ℝ) := by
  have hr : (113.534135835879 : ℝ) ≤ √(12890 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.534135835879 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12890 12890 (11 / 1000) ≤
    (0.008419379492 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12890) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.534135835879 : ℝ) ≤ √(12890 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12890)
  have hdiv : K / √(12890 : ℝ) ≤ K / 113.534135835879 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.534135835879 ≤ (0.008419379492 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12890.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12890 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12890 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12890 := gPlus_lower 12890
end BstLean.Part269.N12890

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12890
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035542012672 : ℝ) ≤ wn 12890 := by
  have hn : √(12890 : ℝ) ≤ 113.534135835880 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12890 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.534135835880 ≤ 2 / √(12890 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248104098 : ℝ) ≤ rhoBar 12890 BstLean.Part154.csC ∧
    rhoBar 12890 BstLean.Part154.csC ≤ 0.000248104482 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035542012672 : ℝ) / (1.295212 * 12890) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035542012673 : ℝ) / (1.29521 * 12890) := by gcongr
      _ ≤ (0.000248104482 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12890 BstLean.Part154.csC) ≤ 0.000992479484 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12890 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12890 BstLean.Part154.csC) (piBar (rhoBar 12890 BstLean.Part154.csC)) ≤ 0.000189503745 ∧
    cc1 (rhoBar 12890 BstLean.Part154.csC) (piBar (rhoBar 12890 BstLean.Part154.csC)) ≤ 0.000120582518 ∧
    cc2 (rhoBar 12890 BstLean.Part154.csC) ≤ 0.000069999109 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12890 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12890 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12890 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12890 BstLean.Part154.csC * nuR (rhoBar 12890 BstLean.Part154.csC)) ≤ 0.000496224353 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248104482 : ℝ) * 0.000992479484 := by gcongr
      _ ≤ (0.000496224353 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12890 BstLean.Part154.csC) * nuR (rhoBar 12890 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000992479484 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12890 BstLean.Part154.csC) * rhoBar 12890 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248104482 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248104482 / 2 + 0.399 * 0.000992479484 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189503745 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496224353 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120582518 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248104482 / 1.414213562 := by gcongr
      _ ≤ (0.000069999109 : ℝ) := by norm_num

end BstLean.Part269.N12890

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12890
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12890 BstLean.Part154.csC) (piBar (rhoBar 12890 BstLean.Part154.csC)) ≤ 1.55086E-7 := by
  have hr0 : 0 ≤ rhoBar 12890 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12890 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12890 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12890 BstLean.Part154.csC) (piBar (rhoBar 12890 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12890 BstLean.Part154.csC) (piBar (rhoBar 12890 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12890 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189503745 : ℝ) ^ 2 + 0.000120582518 ^ 2 + 3 * 0.000069999109 ^ 2 +
        2 * 0.797885 * 0.000189503745 * 0.000120582518 + 2 * 0.000189503745 * 0.000069999109 +
        4 * 0.797885 * 0.000120582518 * 0.000069999109 := by gcongr
    _ ≤ (1.55086E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12890 BstLean.Part154.csC Θ ≤ 0.002589204611 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12890 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12890 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12890 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12890 BstLean.Part154.csC) (piBar (rhoBar 12890 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12890 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035542012673 * 1.55086E-7 / (0.000248104098 : ℝ) := by gcongr
    _ ≤ 0.002589204611 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12890 BstLean.Part154.csC Θ ≤ 0.002872109519 + 0.000654248202 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12890 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12890 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12890 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035542012673 : ℝ) * ((2 * Θ * 0.000248104482 +
        (6863 / 10000) * 0.000248104482 * 12890 * 0.000992479484) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002872109519 + 0.000654248202 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12890 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12890 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12890 0.011 Θ ∧ gammaRatio 12890 0.011 Θ ≤ 0.000085291905 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12890 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035542012673 : ℝ) * 0.525 / ((1 - 0.011) * 12890) := by gcongr
      _ ≤ (0.000085291905 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12890 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12890 0.011 Θ) :=
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
    badAllowance 12890 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12890 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12890 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12890 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12890 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12890 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12890 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12890 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12890 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12890 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12890 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035542012673 : ℝ) * 12890 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12890 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003335145574 + 0.003243452813 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12890

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12890
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12890 BstLean.Part154.csC) (piBar (rhoBar 12890 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12890 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12890 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12890 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12890 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12890 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12890 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12890 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12890 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12890 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12890 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12890 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12890 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12890 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12890 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052091885730 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12890) ≤ 0.010518753433 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12890 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035542012673)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010518753433 + 2 * 0.737676 / 12890) := by gcongr
    _ ≤ (0.052091885730 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12890 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12890

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12890
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512034003 : ℝ) ≤ plow 12890 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12890) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052544558301)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359332421) : eMP 12890 0.011 xi bn ≤ 0.001170507911 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12890 : ℝ) * (1 - 0.011))) ≤ 0.000578779571 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001359332421 / (12890 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578779571 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578779571 : ℝ) + 3.141593 * 0.052544558301 / (12890 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001170507911 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052544558301)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359332421) : PiBarMP 12890 12 0.011 xi bn ≤ 0.160046246653 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12890 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036869125580 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.907971374921 : ℝ) ≤ √((12890 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.534135835879 : ℝ) ≤ √(12890 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12890) ≤ 0.122715588226 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036869125580 + 0.052544558301 * 1.772454 / (2 * (112.907971374921 : ℝ))) * (1 + 0.001170507911) +
        8 / (12890 * 113.534135835879) + 0.122715588226 := by gcongr
    _ ≤ (0.160046246653 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052544558301)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359332421) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281317884040) :
    parallelOracle 12890 0.011 xi bn cd ≤ 0.161021804401 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12890 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12890 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512034003 : ℝ) ≤ plow 12890 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.534135835879 : ℝ) ≤ √(12890 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281317884040 : ℝ) / (2 * 0.560512034003 * 113.534135835879)) * 0.160046246653 +
        0.281317884040 ^ 2 / (2 * 0.560512034003 * 113.534135835879) := by gcongr
    _ ≤ (0.161021804401 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052544558301) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359332421)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281317884040) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12890 12890 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512034003 : ℝ) ≤ plow 12890 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.534135835879 : ℝ) ≤ √(12890 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12890 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12890 Θ 1.22 ≤ 0.011680191955 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.534135835879 := by gcongr <;> linarith
      _ ≤ (0.011680191955 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12890 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12890 12890 0.011 ≤ 0.008419379492 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12890 12890 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12890 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12890 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12890 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12890 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161021804401 + 0.011680191955 + (0.008419379492 : ℝ) *
        (1 + 2 * (0.281317884040 + 0.011680191955) / (0.560512034003 * 113.534135835879))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12890]

end BstLean.Part269.N12890

/-! The original eight local profiles supply actual 12890 moment certificates. -/
namespace BstLean.Part269.N12890
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12890 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12890 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12890 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052544558301 ∧
    0 ≤ bN 12890 BstLean.Part154.csC (groupTheta g) ∧ bN 12890 BstLean.Part154.csC (groupTheta g) ≤ 0.001359332421 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12890 12890 0.011
      (momentAllowance 12890 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12890 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12890 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12890 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12890 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12890 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229225998310 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12890 0.011
      (momentAllowance 12890 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12890 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12890
/-! The actual computed-centre upper energy formula at 12890. -/
namespace BstLean.Part269.N12890
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12890

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12890
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12890)
open BstLean.Part268 (cell12890)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084954543477
  | 2 => 0.085887853920
  | 3 => 0.086817993203
  | 4 => 0.087746073006
  | 5 => 0.088673447322
  | 6 => 0.089601749643
  | 7 => 0.090532933843
  | 8 => 0.091469318882
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12890 12890 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12890 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003338665865 + 0.003247348463 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S21.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12890

/-! Actual upper energy certificates on all 43 source endpoints at 12890. -/
namespace BstLean.Part269.N12890
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12890)
open BstLean.Part268 (cell12890)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12890 (gMinus 12890) (1 - (cell12890 i).lower) ≤ 1 ∧
    energyUpper 12890 (gMinus 12890) (BstLean.Part211.gPlus 12890)
      (finiteEnergy 12890 12890 0.011) (1 - (cell12890 i).lower) ≤
      (cell12890 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨10,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨11,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨12,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨13,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨14,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨15,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨16,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨17,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨18,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨19,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨20,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨21,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨22,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨23,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨24,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨25,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨26,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨27,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨28,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨29,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨30,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨31,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨32,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨33,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨34,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨35,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨36,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨37,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨38,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨39,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨40,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨41,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨42,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨43,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨44,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨45,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨46,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨47,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨48,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨49,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨50,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨51,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12890) (by norm_num)
        (q := 1 - (cell12890 ⟨52,by decide⟩).lower)
        (by norm_num [cell12890]) (by norm_num [cell12890])
      exact ⟨E.1,E.2.trans (by norm_num [cell12890])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12890

/-! Source-cell containment and simple scalar guards at 12890. -/
namespace BstLean.Part269.N12890
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12890)
open BstLean.Part268 (cell12890)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12890 ⟨10,by decide⟩).lower ∧ (cell12890 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12890 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12890 ⟨11,by decide⟩).lower ∧ (cell12890 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12890 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12890 ⟨12,by decide⟩).lower ∧ (cell12890 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12890 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12890 ⟨13,by decide⟩).lower ∧ (cell12890 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12890 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12890 ⟨14,by decide⟩).lower ∧ (cell12890 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12890 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12890 ⟨15,by decide⟩).lower ∧ (cell12890 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12890 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12890 ⟨16,by decide⟩).lower ∧ (cell12890 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12890 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12890 ⟨17,by decide⟩).lower ∧ (cell12890 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12890 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12890 ⟨18,by decide⟩).lower ∧ (cell12890 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12890 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12890 ⟨19,by decide⟩).lower ∧ (cell12890 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12890 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12890 ⟨20,by decide⟩).lower ∧ (cell12890 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12890 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12890 ⟨21,by decide⟩).lower ∧ (cell12890 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12890 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12890 ⟨22,by decide⟩).lower ∧ (cell12890 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12890 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12890 ⟨23,by decide⟩).lower ∧ (cell12890 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12890 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12890 ⟨24,by decide⟩).lower ∧ (cell12890 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12890 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12890 ⟨25,by decide⟩).lower ∧ (cell12890 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12890 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12890 ⟨26,by decide⟩).lower ∧ (cell12890 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12890 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12890 ⟨27,by decide⟩).lower ∧ (cell12890 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12890 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12890 ⟨28,by decide⟩).lower ∧ (cell12890 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12890 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12890 ⟨29,by decide⟩).lower ∧ (cell12890 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12890 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12890 ⟨30,by decide⟩).lower ∧ (cell12890 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12890 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12890 ⟨31,by decide⟩).lower ∧ (cell12890 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12890 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12890 ⟨32,by decide⟩).lower ∧ (cell12890 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12890 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12890 ⟨33,by decide⟩).lower ∧ (cell12890 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12890 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12890 ⟨34,by decide⟩).lower ∧ (cell12890 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12890 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12890 ⟨35,by decide⟩).lower ∧ (cell12890 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12890 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12890 ⟨36,by decide⟩).lower ∧ (cell12890 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12890 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12890 ⟨37,by decide⟩).lower ∧ (cell12890 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12890 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12890 ⟨38,by decide⟩).lower ∧ (cell12890 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12890 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12890 ⟨39,by decide⟩).lower ∧ (cell12890 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12890 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12890 ⟨40,by decide⟩).lower ∧ (cell12890 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12890 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12890 ⟨41,by decide⟩).lower ∧ (cell12890 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12890 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12890 ⟨42,by decide⟩).lower ∧ (cell12890 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12890 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12890 ⟨43,by decide⟩).lower ∧ (cell12890 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12890 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12890 ⟨44,by decide⟩).lower ∧ (cell12890 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12890 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12890 ⟨45,by decide⟩).lower ∧ (cell12890 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12890 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12890 ⟨46,by decide⟩).lower ∧ (cell12890 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12890 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12890 ⟨47,by decide⟩).lower ∧ (cell12890 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12890 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12890 ⟨48,by decide⟩).lower ∧ (cell12890 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12890 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12890 ⟨49,by decide⟩).lower ∧ (cell12890 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12890 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12890 ⟨50,by decide⟩).lower ∧ (cell12890 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12890 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12890 ⟨51,by decide⟩).lower ∧ (cell12890 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12890 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12890 ⟨52,by decide⟩).lower ∧ (cell12890 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12890 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12890 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12890 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12890,cell12890,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12890 i).lower ∧
    (cell12890 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12890 i).upper ≤ (0.532 : ℝ) ∧
    (cell12890 i).centre ≤ (0.1 : ℝ) ∧ (cell12890 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12890 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12890 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12890

/-! The local source numeric instances at 12890 have no network premises. -/
namespace BstLean.Part269.N12890
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12890)
open BstLean.Part268 (cell12890)

noncomputable def sourceNumerics12890 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12890 (cell12890 i)
      scalarRow12890.M scalarRow12890.H scalarRow12890.xi := by
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
    energy_allowance := scalarRow12890.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12890]
    centre_nonneg := (scalarRow12890.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12890])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12890
/-! Actual 12891 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12891
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12891 ≤ (1.035540622051 : ℝ) := by
  have hr : (113.538539712293 : ℝ) ≤ √(12891 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.538539712293 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12891 12891 (11 / 1000) ≤
    (0.008419052923 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12891) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.538539712293 : ℝ) ≤ √(12891 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12891)
  have hdiv : K / √(12891 : ℝ) ≤ K / 113.538539712293 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.538539712293 ≤ (0.008419052923 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12891.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12891 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12891 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12891 := gPlus_lower 12891
end BstLean.Part269.N12891

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12891
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035540622050 : ℝ) ≤ wn 12891 := by
  have hn : √(12891 : ℝ) ≤ 113.538539712294 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12891 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.538539712294 ≤ 2 / √(12891 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248084518 : ℝ) ≤ rhoBar 12891 BstLean.Part154.csC ∧
    rhoBar 12891 BstLean.Part154.csC ≤ 0.000248084902 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035540622050 : ℝ) / (1.295212 * 12891) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035540622051 : ℝ) / (1.29521 * 12891) := by gcongr
      _ ≤ (0.000248084902 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12891 BstLean.Part154.csC) ≤ 0.000992401155 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12891 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12891 BstLean.Part154.csC) (piBar (rhoBar 12891 BstLean.Part154.csC)) ≤ 0.000189488789 ∧
    cc1 (rhoBar 12891 BstLean.Part154.csC) (piBar (rhoBar 12891 BstLean.Part154.csC)) ≤ 0.000120573002 ∧
    cc2 (rhoBar 12891 BstLean.Part154.csC) ≤ 0.000069993585 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12891 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12891 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12891 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12891 BstLean.Part154.csC * nuR (rhoBar 12891 BstLean.Part154.csC)) ≤ 0.000496185191 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248084902 : ℝ) * 0.000992401155 := by gcongr
      _ ≤ (0.000496185191 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12891 BstLean.Part154.csC) * nuR (rhoBar 12891 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000992401155 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12891 BstLean.Part154.csC) * rhoBar 12891 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248084902 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248084902 / 2 + 0.399 * 0.000992401155 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189488789 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496185191 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120573002 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248084902 / 1.414213562 := by gcongr
      _ ≤ (0.000069993585 : ℝ) := by norm_num

end BstLean.Part269.N12891

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12891
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12891 BstLean.Part154.csC) (piBar (rhoBar 12891 BstLean.Part154.csC)) ≤ 1.55061E-7 := by
  have hr0 : 0 ≤ rhoBar 12891 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12891 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12891 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12891 BstLean.Part154.csC) (piBar (rhoBar 12891 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12891 BstLean.Part154.csC) (piBar (rhoBar 12891 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12891 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189488789 : ℝ) ^ 2 + 0.000120573002 ^ 2 + 3 * 0.000069993585 ^ 2 +
        2 * 0.797885 * 0.000189488789 * 0.000120573002 + 2 * 0.000189488789 * 0.000069993585 +
        4 * 0.797885 * 0.000120573002 * 0.000069993585 := by gcongr
    _ ≤ (1.55061E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12891 BstLean.Part154.csC Θ ≤ 0.002588988071 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12891 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12891 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12891 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12891 BstLean.Part154.csC) (piBar (rhoBar 12891 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12891 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035540622051 * 1.55061E-7 / (0.000248084518 : ℝ) := by gcongr
    _ ≤ 0.002588988071 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12891 BstLean.Part154.csC Θ ≤ 0.002871875126 + 0.000654195692 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12891 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12891 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12891 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035540622051 : ℝ) * ((2 * Θ * 0.000248084902 +
        (6863 / 10000) * 0.000248084902 * 12891 * 0.000992401155) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002871875126 + 0.000654195692 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12891 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12891 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12891 0.011 Θ ∧ gammaRatio 12891 0.011 Θ ≤ 0.000085285174 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12891 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035540622051 : ℝ) * 0.525 / ((1 - 0.011) * 12891) := by gcongr
      _ ≤ (0.000085285174 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12891 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12891 0.011 Θ) :=
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
    badAllowance 12891 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12891 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12891 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12891 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12891 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12891 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12891 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12891 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12891 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12891 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12891 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035540622051 : ℝ) * 12891 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12891 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003334911181 + 0.003243183763 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12891

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12891
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12891 BstLean.Part154.csC) (piBar (rhoBar 12891 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12891 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12891 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12891 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12891 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12891 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12891 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12891 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12891 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12891 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12891 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12891 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12891 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12891 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12891 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052089843469 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12891) ≤ 0.010518345437 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12891 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035540622051)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010518345437 + 2 * 0.737676 / 12891) := by gcongr
    _ ≤ (0.052089843469 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12891 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12891

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12891
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512077899 : ℝ) ≤ plow 12891 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12891) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052544182657)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359218738) : eMP 12891 0.011 xi bn ≤ 0.001170413512 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12891 : ℝ) * (1 - 0.011))) ≤ 0.000578732920 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001359218738 / (12891 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578732920 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578732920 : ℝ) + 3.141593 * 0.052544182657 / (12891 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001170413512 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052544182657)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359218738) : PiBarMP 12891 12 0.011 xi bn ≤ 0.160039920153 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12891 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036867583838 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.912350963036 : ℝ) ≤ √((12891 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.538539712293 : ℝ) ≤ √(12891 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12891) ≤ 0.122710828395 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036867583838 + 0.052544182657 * 1.772454 / (2 * (112.912350963036 : ℝ))) * (1 + 0.001170413512) +
        8 / (12891 * 113.538539712293) + 0.122710828395 := by gcongr
    _ ≤ (0.160039920153 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052544182657)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359218738) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281315022403) :
    parallelOracle 12891 0.011 xi bn cd ≤ 0.161015409754 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12891 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12891 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512077899 : ℝ) ≤ plow 12891 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.538539712293 : ℝ) ≤ √(12891 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281315022403 : ℝ) / (2 * 0.560512077899 * 113.538539712293)) * 0.160039920153 +
        0.281315022403 ^ 2 / (2 * 0.560512077899 * 113.538539712293) := by gcongr
    _ ≤ (0.161015409754 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052544182657) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359218738)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281315022403) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12891 12891 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512077899 : ℝ) ≤ plow 12891 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.538539712293 : ℝ) ≤ √(12891 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12891 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12891 Θ 1.22 ≤ 0.011679738910 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.538539712293 := by gcongr <;> linarith
      _ ≤ (0.011679738910 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12891 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12891 12891 0.011 ≤ 0.008419052923 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12891 12891 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12891 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12891 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12891 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12891 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161015409754 + 0.011679738910 + (0.008419052923 : ℝ) *
        (1 + 2 * (0.281315022403 + 0.011679738910) / (0.560512077899 * 113.538539712293))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12891]

end BstLean.Part269.N12891

/-! The original eight local profiles supply actual 12891 moment certificates. -/
namespace BstLean.Part269.N12891
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12891 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12891 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12891 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052544182657 ∧
    0 ≤ bN 12891 BstLean.Part154.csC (groupTheta g) ∧ bN 12891 BstLean.Part154.csC (groupTheta g) ≤ 0.001359218738 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12891 12891 0.011
      (momentAllowance 12891 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12891 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12891 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12891 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12891 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12891 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229225178934 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12891 0.011
      (momentAllowance 12891 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12891 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12891
/-! The actual computed-centre upper energy formula at 12891. -/
namespace BstLean.Part269.N12891
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12891

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12891
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12891)
open BstLean.Part268 (cell12891)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084951815285
  | 2 => 0.085885079662
  | 3 => 0.086815166830
  | 4 => 0.087743187032
  | 5 => 0.088670492564
  | 6 => 0.089598714922
  | 7 => 0.090529805660
  | 8 => 0.091466081043
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12891 12891 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12891 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003338665865 + 0.003247348463 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S21.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12891

/-! Actual upper energy certificates on all 43 source endpoints at 12891. -/
namespace BstLean.Part269.N12891
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12891)
open BstLean.Part268 (cell12891)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12891 (gMinus 12891) (1 - (cell12891 i).lower) ≤ 1 ∧
    energyUpper 12891 (gMinus 12891) (BstLean.Part211.gPlus 12891)
      (finiteEnergy 12891 12891 0.011) (1 - (cell12891 i).lower) ≤
      (cell12891 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨10,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨11,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨12,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨13,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨14,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨15,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨16,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨17,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨18,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨19,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨20,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨21,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨22,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨23,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨24,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨25,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨26,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨27,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨28,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨29,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨30,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨31,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨32,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨33,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨34,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨35,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨36,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨37,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨38,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨39,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨40,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨41,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨42,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨43,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨44,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨45,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨46,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨47,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨48,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨49,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨50,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨51,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12891) (by norm_num)
        (q := 1 - (cell12891 ⟨52,by decide⟩).lower)
        (by norm_num [cell12891]) (by norm_num [cell12891])
      exact ⟨E.1,E.2.trans (by norm_num [cell12891])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12891

/-! Source-cell containment and simple scalar guards at 12891. -/
namespace BstLean.Part269.N12891
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12891)
open BstLean.Part268 (cell12891)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12891 ⟨10,by decide⟩).lower ∧ (cell12891 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12891 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12891 ⟨11,by decide⟩).lower ∧ (cell12891 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12891 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12891 ⟨12,by decide⟩).lower ∧ (cell12891 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12891 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12891 ⟨13,by decide⟩).lower ∧ (cell12891 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12891 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12891 ⟨14,by decide⟩).lower ∧ (cell12891 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12891 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12891 ⟨15,by decide⟩).lower ∧ (cell12891 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12891 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12891 ⟨16,by decide⟩).lower ∧ (cell12891 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12891 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12891 ⟨17,by decide⟩).lower ∧ (cell12891 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12891 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12891 ⟨18,by decide⟩).lower ∧ (cell12891 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12891 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12891 ⟨19,by decide⟩).lower ∧ (cell12891 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12891 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12891 ⟨20,by decide⟩).lower ∧ (cell12891 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12891 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12891 ⟨21,by decide⟩).lower ∧ (cell12891 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12891 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12891 ⟨22,by decide⟩).lower ∧ (cell12891 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12891 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12891 ⟨23,by decide⟩).lower ∧ (cell12891 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12891 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12891 ⟨24,by decide⟩).lower ∧ (cell12891 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12891 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12891 ⟨25,by decide⟩).lower ∧ (cell12891 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12891 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12891 ⟨26,by decide⟩).lower ∧ (cell12891 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12891 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12891 ⟨27,by decide⟩).lower ∧ (cell12891 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12891 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12891 ⟨28,by decide⟩).lower ∧ (cell12891 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12891 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12891 ⟨29,by decide⟩).lower ∧ (cell12891 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12891 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12891 ⟨30,by decide⟩).lower ∧ (cell12891 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12891 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12891 ⟨31,by decide⟩).lower ∧ (cell12891 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12891 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12891 ⟨32,by decide⟩).lower ∧ (cell12891 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12891 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12891 ⟨33,by decide⟩).lower ∧ (cell12891 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12891 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12891 ⟨34,by decide⟩).lower ∧ (cell12891 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12891 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12891 ⟨35,by decide⟩).lower ∧ (cell12891 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12891 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12891 ⟨36,by decide⟩).lower ∧ (cell12891 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12891 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12891 ⟨37,by decide⟩).lower ∧ (cell12891 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12891 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12891 ⟨38,by decide⟩).lower ∧ (cell12891 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12891 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12891 ⟨39,by decide⟩).lower ∧ (cell12891 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12891 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12891 ⟨40,by decide⟩).lower ∧ (cell12891 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12891 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12891 ⟨41,by decide⟩).lower ∧ (cell12891 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12891 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12891 ⟨42,by decide⟩).lower ∧ (cell12891 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12891 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12891 ⟨43,by decide⟩).lower ∧ (cell12891 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12891 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12891 ⟨44,by decide⟩).lower ∧ (cell12891 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12891 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12891 ⟨45,by decide⟩).lower ∧ (cell12891 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12891 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12891 ⟨46,by decide⟩).lower ∧ (cell12891 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12891 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12891 ⟨47,by decide⟩).lower ∧ (cell12891 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12891 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12891 ⟨48,by decide⟩).lower ∧ (cell12891 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12891 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12891 ⟨49,by decide⟩).lower ∧ (cell12891 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12891 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12891 ⟨50,by decide⟩).lower ∧ (cell12891 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12891 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12891 ⟨51,by decide⟩).lower ∧ (cell12891 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12891 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12891 ⟨52,by decide⟩).lower ∧ (cell12891 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12891 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12891 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12891 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12891,cell12891,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12891 i).lower ∧
    (cell12891 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12891 i).upper ≤ (0.532 : ℝ) ∧
    (cell12891 i).centre ≤ (0.1 : ℝ) ∧ (cell12891 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12891 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12891 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12891

/-! The local source numeric instances at 12891 have no network premises. -/
namespace BstLean.Part269.N12891
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12891)
open BstLean.Part268 (cell12891)

noncomputable def sourceNumerics12891 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12891 (cell12891 i)
      scalarRow12891.M scalarRow12891.H scalarRow12891.xi := by
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
    energy_allowance := scalarRow12891.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12891]
    centre_nonneg := (scalarRow12891.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12891])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12891
/-! Actual 12892 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12892
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12892 ≤ (1.035539231592 : ℝ) := by
  have hr : (113.542943417898 : ℝ) ≤ √(12892 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.542943417898 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12892 12892 (11 / 1000) ≤
    (0.008418726392 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12892) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.542943417898 : ℝ) ≤ √(12892 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12892)
  have hdiv : K / √(12892 : ℝ) ≤ K / 113.542943417898 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.542943417898 ≤ (0.008418726392 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12892.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12892 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12892 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12892 := gPlus_lower 12892
end BstLean.Part269.N12892

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12892
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035539231591 : ℝ) ≤ wn 12892 := by
  have hn : √(12892 : ℝ) ≤ 113.542943417899 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12892 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.542943417899 ≤ 2 / √(12892 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248064942 : ℝ) ≤ rhoBar 12892 BstLean.Part154.csC ∧
    rhoBar 12892 BstLean.Part154.csC ≤ 0.000248065326 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035539231591 : ℝ) / (1.295212 * 12892) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035539231592 : ℝ) / (1.29521 * 12892) := by gcongr
      _ ≤ (0.000248065326 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12892 BstLean.Part154.csC) ≤ 0.000992322841 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12892 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12892 BstLean.Part154.csC) (piBar (rhoBar 12892 BstLean.Part154.csC)) ≤ 0.000189473836 ∧
    cc1 (rhoBar 12892 BstLean.Part154.csC) (piBar (rhoBar 12892 BstLean.Part154.csC)) ≤ 0.000120563487 ∧
    cc2 (rhoBar 12892 BstLean.Part154.csC) ≤ 0.000069988062 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12892 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12892 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12892 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12892 BstLean.Part154.csC * nuR (rhoBar 12892 BstLean.Part154.csC)) ≤ 0.000496146037 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248065326 : ℝ) * 0.000992322841 := by gcongr
      _ ≤ (0.000496146037 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12892 BstLean.Part154.csC) * nuR (rhoBar 12892 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000992322841 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12892 BstLean.Part154.csC) * rhoBar 12892 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248065326 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248065326 / 2 + 0.399 * 0.000992322841 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189473836 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496146037 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120563487 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248065326 / 1.414213562 := by gcongr
      _ ≤ (0.000069988062 : ℝ) := by norm_num

end BstLean.Part269.N12892

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12892
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12892 BstLean.Part154.csC) (piBar (rhoBar 12892 BstLean.Part154.csC)) ≤ 1.55037E-7 := by
  have hr0 : 0 ≤ rhoBar 12892 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12892 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12892 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12892 BstLean.Part154.csC) (piBar (rhoBar 12892 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12892 BstLean.Part154.csC) (piBar (rhoBar 12892 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12892 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189473836 : ℝ) ^ 2 + 0.000120563487 ^ 2 + 3 * 0.000069988062 ^ 2 +
        2 * 0.797885 * 0.000189473836 * 0.000120563487 + 2 * 0.000189473836 * 0.000069988062 +
        4 * 0.797885 * 0.000120563487 * 0.000069988062 := by gcongr
    _ ≤ (1.55037E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12892 BstLean.Part154.csC Θ ≤ 0.002588788155 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12892 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12892 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12892 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12892 BstLean.Part154.csC) (piBar (rhoBar 12892 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12892 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035539231592 * 1.55037E-7 / (0.000248064942 : ℝ) := by gcongr
    _ ≤ 0.002588788155 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12892 BstLean.Part154.csC Θ ≤ 0.002871640789 + 0.000654143192 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12892 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12892 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12892 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035539231592 : ℝ) * ((2 * Θ * 0.000248065326 +
        (6863 / 10000) * 0.000248065326 * 12892 * 0.000992322841) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002871640789 + 0.000654143192 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12892 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12892 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12892 0.011 Θ ∧ gammaRatio 12892 0.011 Θ ≤ 0.000085278444 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12892 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035539231592 : ℝ) * 0.525 / ((1 - 0.011) * 12892) := by gcongr
      _ ≤ (0.000085278444 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12892 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12892 0.011 Θ) :=
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
    badAllowance 12892 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12892 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12892 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12892 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12892 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12892 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12892 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12892 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12892 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12892 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12892 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035539231592 : ℝ) * 12892 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12892 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003334676844 + 0.003242931347 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12892

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12892
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12892 BstLean.Part154.csC) (piBar (rhoBar 12892 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12892 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12892 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12892 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12892 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12892 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12892 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12892 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12892 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12892 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12892 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12892 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12892 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12892 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12892 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052087801444 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12892) ≤ 0.010517937488 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12892 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035539231592)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010517937488 + 2 * 0.737676 / 12892) := by gcongr
    _ ≤ (0.052087801444 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12892 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12892

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12892
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512121788 : ℝ) ≤ plow 12892 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12892) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052543815802)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359113782) : eMP 12892 0.011 xi bn ≤ 0.001170322839 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12892 : ℝ) * (1 - 0.011))) ≤ 0.000578688131 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001359113782 / (12892 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578688131 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578688131 : ℝ) + 3.141593 * 0.052543815802 / (12892 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001170322839 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052543815802)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359113782) : PiBarMP 12892 12 0.011 xi bn ≤ 0.160033712850 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12892 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036866160392 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.916730381285 : ℝ) ≤ √((12892 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.542943417898 : ℝ) ≤ √(12892 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12892) ≤ 0.122706069117 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036866160392 + 0.052543815802 * 1.772454 / (2 * (112.916730381285 : ℝ))) * (1 + 0.001170322839) +
        8 / (12892 * 113.542943417898) + 0.122706069117 := by gcongr
    _ ≤ (0.160033712850 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052543815802)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359113782) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281312180170) :
    parallelOracle 12892 0.011 xi bn cd ≤ 0.161009134685 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12892 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12892 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512121788 : ℝ) ≤ plow 12892 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.542943417898 : ℝ) ≤ √(12892 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281312180170 : ℝ) / (2 * 0.560512121788 * 113.542943417898)) * 0.160033712850 +
        0.281312180170 ^ 2 / (2 * 0.560512121788 * 113.542943417898) := by gcongr
    _ ≤ (0.161009134685 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052543815802) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359113782)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281312180170) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12892 12892 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512121788 : ℝ) ≤ plow 12892 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.542943417898 : ℝ) ≤ √(12892 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12892 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12892 Θ 1.22 ≤ 0.011679285917 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.542943417898 := by gcongr <;> linarith
      _ ≤ (0.011679285917 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12892 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12892 12892 0.011 ≤ 0.008418726392 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12892 12892 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12892 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12892 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12892 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12892 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161009134685 + 0.011679285917 + (0.008418726392 : ℝ) *
        (1 + 2 * (0.281312180170 + 0.011679285917) / (0.560512121788 * 113.542943417898))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12892]

end BstLean.Part269.N12892

/-! The original eight local profiles supply actual 12892 moment certificates. -/
namespace BstLean.Part269.N12892
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12892 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12892 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12892 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052543815802 ∧
    0 ≤ bN 12892 BstLean.Part154.csC (groupTheta g) ∧ bN 12892 BstLean.Part154.csC (groupTheta g) ≤ 0.001359113782 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12892 12892 0.011
      (momentAllowance 12892 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12892 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12892 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12892 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12892 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12892 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229224378726 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12892 0.011
      (momentAllowance 12892 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12892 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12892
/-! The actual computed-centre upper energy formula at 12892. -/
namespace BstLean.Part269.N12892
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12892

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12892
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12892)
open BstLean.Part268 (cell12892)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084949087991
  | 2 => 0.085882306336
  | 3 => 0.086812341433
  | 4 => 0.087740302086
  | 5 => 0.088667538898
  | 6 => 0.089595681374
  | 7 => 0.090526678745
  | 8 => 0.091462844588
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12892 12892 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12892 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003338665865 + 0.003247348463 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S21.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12892

/-! Actual upper energy certificates on all 43 source endpoints at 12892. -/
namespace BstLean.Part269.N12892
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12892)
open BstLean.Part268 (cell12892)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12892 (gMinus 12892) (1 - (cell12892 i).lower) ≤ 1 ∧
    energyUpper 12892 (gMinus 12892) (BstLean.Part211.gPlus 12892)
      (finiteEnergy 12892 12892 0.011) (1 - (cell12892 i).lower) ≤
      (cell12892 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨10,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨11,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨12,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨13,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨14,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨15,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨16,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨17,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨18,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨19,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨20,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨21,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨22,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨23,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨24,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨25,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨26,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨27,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨28,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨29,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨30,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨31,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨32,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨33,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨34,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨35,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨36,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨37,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨38,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨39,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨40,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨41,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨42,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨43,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨44,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨45,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨46,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨47,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨48,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨49,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨50,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨51,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12892) (by norm_num)
        (q := 1 - (cell12892 ⟨52,by decide⟩).lower)
        (by norm_num [cell12892]) (by norm_num [cell12892])
      exact ⟨E.1,E.2.trans (by norm_num [cell12892])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12892

/-! Source-cell containment and simple scalar guards at 12892. -/
namespace BstLean.Part269.N12892
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12892)
open BstLean.Part268 (cell12892)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12892 ⟨10,by decide⟩).lower ∧ (cell12892 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12892 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12892 ⟨11,by decide⟩).lower ∧ (cell12892 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12892 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12892 ⟨12,by decide⟩).lower ∧ (cell12892 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12892 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12892 ⟨13,by decide⟩).lower ∧ (cell12892 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12892 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12892 ⟨14,by decide⟩).lower ∧ (cell12892 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12892 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12892 ⟨15,by decide⟩).lower ∧ (cell12892 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12892 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12892 ⟨16,by decide⟩).lower ∧ (cell12892 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12892 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12892 ⟨17,by decide⟩).lower ∧ (cell12892 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12892 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12892 ⟨18,by decide⟩).lower ∧ (cell12892 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12892 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12892 ⟨19,by decide⟩).lower ∧ (cell12892 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12892 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12892 ⟨20,by decide⟩).lower ∧ (cell12892 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12892 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12892 ⟨21,by decide⟩).lower ∧ (cell12892 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12892 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12892 ⟨22,by decide⟩).lower ∧ (cell12892 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12892 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12892 ⟨23,by decide⟩).lower ∧ (cell12892 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12892 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12892 ⟨24,by decide⟩).lower ∧ (cell12892 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12892 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12892 ⟨25,by decide⟩).lower ∧ (cell12892 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12892 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12892 ⟨26,by decide⟩).lower ∧ (cell12892 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12892 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12892 ⟨27,by decide⟩).lower ∧ (cell12892 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12892 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12892 ⟨28,by decide⟩).lower ∧ (cell12892 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12892 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12892 ⟨29,by decide⟩).lower ∧ (cell12892 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12892 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12892 ⟨30,by decide⟩).lower ∧ (cell12892 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12892 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12892 ⟨31,by decide⟩).lower ∧ (cell12892 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12892 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12892 ⟨32,by decide⟩).lower ∧ (cell12892 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12892 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12892 ⟨33,by decide⟩).lower ∧ (cell12892 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12892 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12892 ⟨34,by decide⟩).lower ∧ (cell12892 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12892 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12892 ⟨35,by decide⟩).lower ∧ (cell12892 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12892 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12892 ⟨36,by decide⟩).lower ∧ (cell12892 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12892 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12892 ⟨37,by decide⟩).lower ∧ (cell12892 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12892 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12892 ⟨38,by decide⟩).lower ∧ (cell12892 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12892 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12892 ⟨39,by decide⟩).lower ∧ (cell12892 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12892 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12892 ⟨40,by decide⟩).lower ∧ (cell12892 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12892 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12892 ⟨41,by decide⟩).lower ∧ (cell12892 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12892 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12892 ⟨42,by decide⟩).lower ∧ (cell12892 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12892 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12892 ⟨43,by decide⟩).lower ∧ (cell12892 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12892 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12892 ⟨44,by decide⟩).lower ∧ (cell12892 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12892 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12892 ⟨45,by decide⟩).lower ∧ (cell12892 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12892 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12892 ⟨46,by decide⟩).lower ∧ (cell12892 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12892 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12892 ⟨47,by decide⟩).lower ∧ (cell12892 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12892 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12892 ⟨48,by decide⟩).lower ∧ (cell12892 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12892 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12892 ⟨49,by decide⟩).lower ∧ (cell12892 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12892 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12892 ⟨50,by decide⟩).lower ∧ (cell12892 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12892 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12892 ⟨51,by decide⟩).lower ∧ (cell12892 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12892 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12892 ⟨52,by decide⟩).lower ∧ (cell12892 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12892 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12892 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12892 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12892,cell12892,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12892 i).lower ∧
    (cell12892 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12892 i).upper ≤ (0.532 : ℝ) ∧
    (cell12892 i).centre ≤ (0.1 : ℝ) ∧ (cell12892 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12892 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12892 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12892

/-! The local source numeric instances at 12892 have no network premises. -/
namespace BstLean.Part269.N12892
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12892)
open BstLean.Part268 (cell12892)

noncomputable def sourceNumerics12892 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12892 (cell12892 i)
      scalarRow12892.M scalarRow12892.H scalarRow12892.xi := by
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
    energy_allowance := scalarRow12892.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12892]
    centre_nonneg := (scalarRow12892.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12892])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12892
/-! Actual 12893 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12893
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12893 ≤ (1.035537841295 : ℝ) := by
  have hr : (113.547346952713 : ℝ) ≤ √(12893 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.547346952713 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12893 12893 (11 / 1000) ≤
    (0.008418399899 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12893) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.547346952713 : ℝ) ≤ √(12893 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12893)
  have hdiv : K / √(12893 : ℝ) ≤ K / 113.547346952713 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.547346952713 ≤ (0.008418399899 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12893.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12893 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12893 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12893 := gPlus_lower 12893
end BstLean.Part269.N12893

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12893
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035537841294 : ℝ) ≤ wn 12893 := by
  have hn : √(12893 : ℝ) ≤ 113.547346952714 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12893 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.547346952714 ≤ 2 / √(12893 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248045368 : ℝ) ≤ rhoBar 12893 BstLean.Part154.csC ∧
    rhoBar 12893 BstLean.Part154.csC ≤ 0.000248045752 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035537841294 : ℝ) / (1.295212 * 12893) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035537841295 : ℝ) / (1.29521 * 12893) := by gcongr
      _ ≤ (0.000248045752 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12893 BstLean.Part154.csC) ≤ 0.000992244535 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12893 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12893 BstLean.Part154.csC) (piBar (rhoBar 12893 BstLean.Part154.csC)) ≤ 0.000189458885 ∧
    cc1 (rhoBar 12893 BstLean.Part154.csC) (piBar (rhoBar 12893 BstLean.Part154.csC)) ≤ 0.000120553974 ∧
    cc2 (rhoBar 12893 BstLean.Part154.csC) ≤ 0.000069982539 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12893 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12893 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12893 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12893 BstLean.Part154.csC * nuR (rhoBar 12893 BstLean.Part154.csC)) ≤ 0.000496106886 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248045752 : ℝ) * 0.000992244535 := by gcongr
      _ ≤ (0.000496106886 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12893 BstLean.Part154.csC) * nuR (rhoBar 12893 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000992244535 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12893 BstLean.Part154.csC) * rhoBar 12893 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248045752 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248045752 / 2 + 0.399 * 0.000992244535 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189458885 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496106886 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120553974 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248045752 / 1.414213562 := by gcongr
      _ ≤ (0.000069982539 : ℝ) := by norm_num

end BstLean.Part269.N12893

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12893
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12893 BstLean.Part154.csC) (piBar (rhoBar 12893 BstLean.Part154.csC)) ≤ 1.55012E-7 := by
  have hr0 : 0 ≤ rhoBar 12893 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12893 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12893 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12893 BstLean.Part154.csC) (piBar (rhoBar 12893 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12893 BstLean.Part154.csC) (piBar (rhoBar 12893 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12893 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189458885 : ℝ) ^ 2 + 0.000120553974 ^ 2 + 3 * 0.000069982539 ^ 2 +
        2 * 0.797885 * 0.000189458885 * 0.000120553974 + 2 * 0.000189458885 * 0.000069982539 +
        4 * 0.797885 * 0.000120553974 * 0.000069982539 := by gcongr
    _ ≤ (1.55012E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12893 BstLean.Part154.csC Θ ≤ 0.002588571489 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12893 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12893 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12893 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12893 BstLean.Part154.csC) (piBar (rhoBar 12893 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12893 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035537841295 * 1.55012E-7 / (0.000248045368 : ℝ) := by gcongr
    _ ≤ 0.002588571489 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12893 BstLean.Part154.csC Θ ≤ 0.002871406464 + 0.000654090697 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12893 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12893 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12893 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035537841295 : ℝ) * ((2 * Θ * 0.000248045752 +
        (6863 / 10000) * 0.000248045752 * 12893 * 0.000992244535) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002871406464 + 0.000654090697 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12893 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12893 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12893 0.011 Θ ∧ gammaRatio 12893 0.011 Θ ≤ 0.000085271716 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12893 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035537841295 : ℝ) * 0.525 / ((1 - 0.011) * 12893) := by gcongr
      _ ≤ (0.000085271716 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12893 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12893 0.011 Θ) :=
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
    badAllowance 12893 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12893 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12893 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12893 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12893 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12893 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12893 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12893 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12893 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12893 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12893 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035537841295 : ℝ) * 12893 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12893 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003334442519 + 0.003242662186 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12893

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12893
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12893 BstLean.Part154.csC) (piBar (rhoBar 12893 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12893 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12893 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12893 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12893 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12893 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12893 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12893 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12893 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12893 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12893 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12893 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12893 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12893 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12893 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052085759662 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12893) ≤ 0.010517529587 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12893 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035537841295)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010517529587 + 2 * 0.737676 / 12893) := by gcongr
    _ ≤ (0.052085759662 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12893 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12893

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12893
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512165671 : ℝ) ≤ plow 12893 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12893) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052543440167)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359000032) : eMP 12893 0.011 xi bn ≤ 0.001170228424 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12893 : ℝ) * (1 - 0.011))) ≤ 0.000578641472 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001359000032 / (12893 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578641472 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578641472 : ℝ) + 3.141593 * 0.052543440167 / (12893 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001170228424 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052543440167)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359000032) : PiBarMP 12893 12 0.011 xi bn ≤ 0.160027386428 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12893 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036864617617 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.921109629687 : ℝ) ≤ √((12893 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.547346952713 : ℝ) ≤ √(12893 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12893) ≤ 0.122701310394 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036864617617 + 0.052543440167 * 1.772454 / (2 * (112.921109629687 : ℝ))) * (1 + 0.001170228424) +
        8 / (12893 * 113.547346952713) + 0.122701310394 := by gcongr
    _ ≤ (0.160027386428 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052543440167)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359000032) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281309319025) :
    parallelOracle 12893 0.011 xi bn cd ≤ 0.161002740133 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12893 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12893 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512165671 : ℝ) ≤ plow 12893 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.547346952713 : ℝ) ≤ √(12893 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281309319025 : ℝ) / (2 * 0.560512165671 * 113.547346952713)) * 0.160027386428 +
        0.281309319025 ^ 2 / (2 * 0.560512165671 * 113.547346952713) := by gcongr
    _ ≤ (0.161002740133 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052543440167) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359000032)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281309319025) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12893 12893 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512165671 : ℝ) ≤ plow 12893 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.547346952713 : ℝ) ≤ √(12893 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12893 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12893 Θ 1.22 ≤ 0.011678832977 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.547346952713 := by gcongr <;> linarith
      _ ≤ (0.011678832977 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12893 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12893 12893 0.011 ≤ 0.008418399899 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12893 12893 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12893 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12893 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12893 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12893 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161002740133 + 0.011678832977 + (0.008418399899 : ℝ) *
        (1 + 2 * (0.281309319025 + 0.011678832977) / (0.560512165671 * 113.547346952713))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12893]

end BstLean.Part269.N12893

/-! The original eight local profiles supply actual 12893 moment certificates. -/
namespace BstLean.Part269.N12893
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12893 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12893 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12893 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052543440167 ∧
    0 ≤ bN 12893 BstLean.Part154.csC (groupTheta g) ∧ bN 12893 BstLean.Part154.csC (groupTheta g) ≤ 0.001359000032 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12893 12893 0.011
      (momentAllowance 12893 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12893 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12893 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12893 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12893 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12893 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229223559363 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12893 0.011
      (momentAllowance 12893 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12893 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12893
/-! The actual computed-centre upper energy formula at 12893. -/
namespace BstLean.Part269.N12893
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12893

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12893
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12893)
open BstLean.Part268 (cell12893)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084946361593
  | 2 => 0.085879533943
  | 3 => 0.086809517011
  | 4 => 0.087737418168
  | 5 => 0.088664586325
  | 6 => 0.089592648997
  | 7 => 0.090523553097
  | 8 => 0.091459609514
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12893 12893 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12893 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003338665865 + 0.003247348463 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S21.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12893

/-! Actual upper energy certificates on all 43 source endpoints at 12893. -/
namespace BstLean.Part269.N12893
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12893)
open BstLean.Part268 (cell12893)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12893 (gMinus 12893) (1 - (cell12893 i).lower) ≤ 1 ∧
    energyUpper 12893 (gMinus 12893) (BstLean.Part211.gPlus 12893)
      (finiteEnergy 12893 12893 0.011) (1 - (cell12893 i).lower) ≤
      (cell12893 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨10,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨11,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨12,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨13,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨14,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨15,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨16,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨17,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨18,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨19,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨20,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨21,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨22,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨23,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨24,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨25,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨26,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨27,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨28,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨29,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨30,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨31,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨32,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨33,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨34,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨35,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨36,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨37,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨38,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨39,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨40,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨41,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨42,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨43,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨44,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨45,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨46,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨47,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨48,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨49,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨50,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨51,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12893) (by norm_num)
        (q := 1 - (cell12893 ⟨52,by decide⟩).lower)
        (by norm_num [cell12893]) (by norm_num [cell12893])
      exact ⟨E.1,E.2.trans (by norm_num [cell12893])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12893

/-! Source-cell containment and simple scalar guards at 12893. -/
namespace BstLean.Part269.N12893
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12893)
open BstLean.Part268 (cell12893)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12893 ⟨10,by decide⟩).lower ∧ (cell12893 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12893 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12893 ⟨11,by decide⟩).lower ∧ (cell12893 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12893 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12893 ⟨12,by decide⟩).lower ∧ (cell12893 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12893 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12893 ⟨13,by decide⟩).lower ∧ (cell12893 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12893 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12893 ⟨14,by decide⟩).lower ∧ (cell12893 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12893 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12893 ⟨15,by decide⟩).lower ∧ (cell12893 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12893 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12893 ⟨16,by decide⟩).lower ∧ (cell12893 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12893 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12893 ⟨17,by decide⟩).lower ∧ (cell12893 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12893 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12893 ⟨18,by decide⟩).lower ∧ (cell12893 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12893 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12893 ⟨19,by decide⟩).lower ∧ (cell12893 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12893 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12893 ⟨20,by decide⟩).lower ∧ (cell12893 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12893 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12893 ⟨21,by decide⟩).lower ∧ (cell12893 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12893 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12893 ⟨22,by decide⟩).lower ∧ (cell12893 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12893 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12893 ⟨23,by decide⟩).lower ∧ (cell12893 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12893 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12893 ⟨24,by decide⟩).lower ∧ (cell12893 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12893 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12893 ⟨25,by decide⟩).lower ∧ (cell12893 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12893 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12893 ⟨26,by decide⟩).lower ∧ (cell12893 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12893 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12893 ⟨27,by decide⟩).lower ∧ (cell12893 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12893 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12893 ⟨28,by decide⟩).lower ∧ (cell12893 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12893 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12893 ⟨29,by decide⟩).lower ∧ (cell12893 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12893 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12893 ⟨30,by decide⟩).lower ∧ (cell12893 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12893 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12893 ⟨31,by decide⟩).lower ∧ (cell12893 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12893 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12893 ⟨32,by decide⟩).lower ∧ (cell12893 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12893 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12893 ⟨33,by decide⟩).lower ∧ (cell12893 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12893 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12893 ⟨34,by decide⟩).lower ∧ (cell12893 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12893 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12893 ⟨35,by decide⟩).lower ∧ (cell12893 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12893 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12893 ⟨36,by decide⟩).lower ∧ (cell12893 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12893 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12893 ⟨37,by decide⟩).lower ∧ (cell12893 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12893 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12893 ⟨38,by decide⟩).lower ∧ (cell12893 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12893 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12893 ⟨39,by decide⟩).lower ∧ (cell12893 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12893 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12893 ⟨40,by decide⟩).lower ∧ (cell12893 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12893 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12893 ⟨41,by decide⟩).lower ∧ (cell12893 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12893 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12893 ⟨42,by decide⟩).lower ∧ (cell12893 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12893 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12893 ⟨43,by decide⟩).lower ∧ (cell12893 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12893 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12893 ⟨44,by decide⟩).lower ∧ (cell12893 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12893 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12893 ⟨45,by decide⟩).lower ∧ (cell12893 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12893 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12893 ⟨46,by decide⟩).lower ∧ (cell12893 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12893 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12893 ⟨47,by decide⟩).lower ∧ (cell12893 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12893 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12893 ⟨48,by decide⟩).lower ∧ (cell12893 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12893 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12893 ⟨49,by decide⟩).lower ∧ (cell12893 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12893 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12893 ⟨50,by decide⟩).lower ∧ (cell12893 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12893 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12893 ⟨51,by decide⟩).lower ∧ (cell12893 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12893 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12893 ⟨52,by decide⟩).lower ∧ (cell12893 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12893 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12893 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12893 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12893,cell12893,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12893 i).lower ∧
    (cell12893 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12893 i).upper ≤ (0.532 : ℝ) ∧
    (cell12893 i).centre ≤ (0.1 : ℝ) ∧ (cell12893 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12893 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12893 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12893

/-! The local source numeric instances at 12893 have no network premises. -/
namespace BstLean.Part269.N12893
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12893)
open BstLean.Part268 (cell12893)

noncomputable def sourceNumerics12893 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12893 (cell12893 i)
      scalarRow12893.M scalarRow12893.H scalarRow12893.xi := by
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
    energy_allowance := scalarRow12893.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12893]
    centre_nonneg := (scalarRow12893.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12893])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12893
/-! Actual 12894 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12894
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12894 ≤ (1.035536451161 : ℝ) := by
  have hr : (113.551750316760 : ℝ) ≤ √(12894 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.551750316760 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12894 12894 (11 / 1000) ≤
    (0.008418073444 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12894) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.551750316760 : ℝ) ≤ √(12894 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12894)
  have hdiv : K / √(12894 : ℝ) ≤ K / 113.551750316760 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.551750316760 ≤ (0.008418073444 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12894.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12894 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12894 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12894 := gPlus_lower 12894
end BstLean.Part269.N12894

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12894
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035536451160 : ℝ) ≤ wn 12894 := by
  have hn : √(12894 : ℝ) ≤ 113.551750316761 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12894 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.551750316761 ≤ 2 / √(12894 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248025798 : ℝ) ≤ rhoBar 12894 BstLean.Part154.csC ∧
    rhoBar 12894 BstLean.Part154.csC ≤ 0.000248026182 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035536451160 : ℝ) / (1.295212 * 12894) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035536451161 : ℝ) / (1.29521 * 12894) := by gcongr
      _ ≤ (0.000248026182 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12894 BstLean.Part154.csC) ≤ 0.000992166245 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12894 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12894 BstLean.Part154.csC) (piBar (rhoBar 12894 BstLean.Part154.csC)) ≤ 0.000189443936 ∧
    cc1 (rhoBar 12894 BstLean.Part154.csC) (piBar (rhoBar 12894 BstLean.Part154.csC)) ≤ 0.000120544462 ∧
    cc2 (rhoBar 12894 BstLean.Part154.csC) ≤ 0.000069977018 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12894 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12894 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12894 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12894 BstLean.Part154.csC * nuR (rhoBar 12894 BstLean.Part154.csC)) ≤ 0.000496067744 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248026182 : ℝ) * 0.000992166245 := by gcongr
      _ ≤ (0.000496067744 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12894 BstLean.Part154.csC) * nuR (rhoBar 12894 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000992166245 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12894 BstLean.Part154.csC) * rhoBar 12894 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248026182 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248026182 / 2 + 0.399 * 0.000992166245 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189443936 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496067744 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120544462 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248026182 / 1.414213562 := by gcongr
      _ ≤ (0.000069977018 : ℝ) := by norm_num

end BstLean.Part269.N12894

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12894
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12894 BstLean.Part154.csC) (piBar (rhoBar 12894 BstLean.Part154.csC)) ≤ 1.54988E-7 := by
  have hr0 : 0 ≤ rhoBar 12894 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12894 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12894 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12894 BstLean.Part154.csC) (piBar (rhoBar 12894 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12894 BstLean.Part154.csC) (piBar (rhoBar 12894 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12894 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189443936 : ℝ) ^ 2 + 0.000120544462 ^ 2 + 3 * 0.000069977018 ^ 2 +
        2 * 0.797885 * 0.000189443936 * 0.000120544462 + 2 * 0.000189443936 * 0.000069977018 +
        4 * 0.797885 * 0.000120544462 * 0.000069977018 := by gcongr
    _ ≤ (1.54988E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12894 BstLean.Part154.csC Θ ≤ 0.002588371449 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12894 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12894 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12894 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12894 BstLean.Part154.csC) (piBar (rhoBar 12894 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12894 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035536451161 * 1.54988E-7 / (0.000248025798 : ℝ) := by gcongr
    _ ≤ 0.002588371449 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12894 BstLean.Part154.csC Θ ≤ 0.002871172199 + 0.000654038214 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12894 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12894 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12894 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035536451161 : ℝ) * ((2 * Θ * 0.000248026182 +
        (6863 / 10000) * 0.000248026182 * 12894 * 0.000992166245) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002871172199 + 0.000654038214 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12894 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12894 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12894 0.011 Θ ∧ gammaRatio 12894 0.011 Θ ≤ 0.000085264988 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12894 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035536451161 : ℝ) * 0.525 / ((1 - 0.011) * 12894) := by gcongr
      _ ≤ (0.000085264988 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12894 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12894 0.011 Θ) :=
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
    badAllowance 12894 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12894 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12894 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12894 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12894 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12894 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12894 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12894 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12894 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12894 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12894 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035536451161 : ℝ) * 12894 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12894 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003334208254 + 0.003242409663 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12894

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12894
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12894 BstLean.Part154.csC) (piBar (rhoBar 12894 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12894 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12894 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12894 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12894 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12894 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12894 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12894 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12894 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12894 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12894 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12894 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12894 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12894 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12894 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052083718116 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12894) ≤ 0.010517121733 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12894 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035536451161)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010517121733 + 2 * 0.737676 / 12894) := by gcongr
    _ ≤ (0.052083718116 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12894 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12894

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12894
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512209547 : ℝ) ≤ plow 12894 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12894) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052543073328)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358895011) : eMP 12894 0.011 xi bn ≤ 0.001170137738 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12894 : ℝ) * (1 - 0.011))) ≤ 0.000578596676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001358895011 / (12894 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578596676 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578596676 : ℝ) + 3.141593 * 0.052543073328 / (12894 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001170137738 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052543073328)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358895011) : PiBarMP 12894 12 0.011 xi bn ≤ 0.160021179240 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12894 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036863193175 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.925488708262 : ℝ) ≤ √((12894 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.551750316760 : ℝ) ≤ √(12894 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12894) ≤ 0.122696552223 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036863193175 + 0.052543073328 * 1.772454 / (2 * (112.925488708262 : ℝ))) * (1 + 0.001170137738) +
        8 / (12894 * 113.551750316760) + 0.122696552223 := by gcongr
    _ ≤ (0.160021179240 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052543073328)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358895011) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281306477301) :
    parallelOracle 12894 0.011 xi bn cd ≤ 0.160996465197 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12894 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12894 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512209547 : ℝ) ≤ plow 12894 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.551750316760 : ℝ) ≤ √(12894 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281306477301 : ℝ) / (2 * 0.560512209547 * 113.551750316760)) * 0.160021179240 +
        0.281306477301 ^ 2 / (2 * 0.560512209547 * 113.551750316760) := by gcongr
    _ ≤ (0.160996465197 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052543073328) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358895011)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281306477301) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12894 12894 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512209547 : ℝ) ≤ plow 12894 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.551750316760 : ℝ) ≤ √(12894 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12894 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12894 Θ 1.22 ≤ 0.011678380090 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.551750316760 := by gcongr <;> linarith
      _ ≤ (0.011678380090 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12894 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12894 12894 0.011 ≤ 0.008418073444 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12894 12894 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12894 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12894 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12894 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12894 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160996465197 + 0.011678380090 + (0.008418073444 : ℝ) *
        (1 + 2 * (0.281306477301 + 0.011678380090) / (0.560512209547 * 113.551750316760))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12894]

end BstLean.Part269.N12894

/-! The original eight local profiles supply actual 12894 moment certificates. -/
namespace BstLean.Part269.N12894
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12894 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12894 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12894 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052543073328 ∧
    0 ≤ bN 12894 BstLean.Part154.csC (groupTheta g) ∧ bN 12894 BstLean.Part154.csC (groupTheta g) ≤ 0.001358895011 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12894 12894 0.011
      (momentAllowance 12894 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12894 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12894 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12894 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12894 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12894 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229222759185 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12894 0.011
      (momentAllowance 12894 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12894 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12894
/-! The actual computed-centre upper energy formula at 12894. -/
namespace BstLean.Part269.N12894
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12894

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12894
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12894)
open BstLean.Part268 (cell12894)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084943636093
  | 2 => 0.085876762481
  | 3 => 0.086806693562
  | 4 => 0.087734535277
  | 5 => 0.088661634842
  | 6 => 0.089589617789
  | 7 => 0.090520428714
  | 8 => 0.091456375820
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12894 12894 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12894 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003338665865 + 0.003247348463 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S21.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12894

/-! Actual upper energy certificates on all 43 source endpoints at 12894. -/
namespace BstLean.Part269.N12894
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12894)
open BstLean.Part268 (cell12894)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12894 (gMinus 12894) (1 - (cell12894 i).lower) ≤ 1 ∧
    energyUpper 12894 (gMinus 12894) (BstLean.Part211.gPlus 12894)
      (finiteEnergy 12894 12894 0.011) (1 - (cell12894 i).lower) ≤
      (cell12894 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨10,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨11,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨12,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨13,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨14,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨15,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨16,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨17,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨18,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨19,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨20,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨21,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨22,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨23,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨24,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨25,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨26,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨27,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨28,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨29,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨30,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨31,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨32,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨33,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨34,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨35,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨36,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨37,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨38,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨39,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨40,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨41,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨42,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨43,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨44,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨45,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨46,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨47,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨48,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨49,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨50,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨51,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12894) (by norm_num)
        (q := 1 - (cell12894 ⟨52,by decide⟩).lower)
        (by norm_num [cell12894]) (by norm_num [cell12894])
      exact ⟨E.1,E.2.trans (by norm_num [cell12894])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12894

/-! Source-cell containment and simple scalar guards at 12894. -/
namespace BstLean.Part269.N12894
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12894)
open BstLean.Part268 (cell12894)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12894 ⟨10,by decide⟩).lower ∧ (cell12894 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12894 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12894 ⟨11,by decide⟩).lower ∧ (cell12894 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12894 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12894 ⟨12,by decide⟩).lower ∧ (cell12894 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12894 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12894 ⟨13,by decide⟩).lower ∧ (cell12894 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12894 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12894 ⟨14,by decide⟩).lower ∧ (cell12894 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12894 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12894 ⟨15,by decide⟩).lower ∧ (cell12894 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12894 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12894 ⟨16,by decide⟩).lower ∧ (cell12894 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12894 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12894 ⟨17,by decide⟩).lower ∧ (cell12894 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12894 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12894 ⟨18,by decide⟩).lower ∧ (cell12894 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12894 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12894 ⟨19,by decide⟩).lower ∧ (cell12894 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12894 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12894 ⟨20,by decide⟩).lower ∧ (cell12894 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12894 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12894 ⟨21,by decide⟩).lower ∧ (cell12894 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12894 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12894 ⟨22,by decide⟩).lower ∧ (cell12894 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12894 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12894 ⟨23,by decide⟩).lower ∧ (cell12894 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12894 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12894 ⟨24,by decide⟩).lower ∧ (cell12894 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12894 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12894 ⟨25,by decide⟩).lower ∧ (cell12894 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12894 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12894 ⟨26,by decide⟩).lower ∧ (cell12894 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12894 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12894 ⟨27,by decide⟩).lower ∧ (cell12894 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12894 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12894 ⟨28,by decide⟩).lower ∧ (cell12894 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12894 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12894 ⟨29,by decide⟩).lower ∧ (cell12894 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12894 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12894 ⟨30,by decide⟩).lower ∧ (cell12894 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12894 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12894 ⟨31,by decide⟩).lower ∧ (cell12894 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12894 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12894 ⟨32,by decide⟩).lower ∧ (cell12894 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12894 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12894 ⟨33,by decide⟩).lower ∧ (cell12894 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12894 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12894 ⟨34,by decide⟩).lower ∧ (cell12894 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12894 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12894 ⟨35,by decide⟩).lower ∧ (cell12894 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12894 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12894 ⟨36,by decide⟩).lower ∧ (cell12894 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12894 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12894 ⟨37,by decide⟩).lower ∧ (cell12894 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12894 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12894 ⟨38,by decide⟩).lower ∧ (cell12894 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12894 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12894 ⟨39,by decide⟩).lower ∧ (cell12894 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12894 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12894 ⟨40,by decide⟩).lower ∧ (cell12894 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12894 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12894 ⟨41,by decide⟩).lower ∧ (cell12894 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12894 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12894 ⟨42,by decide⟩).lower ∧ (cell12894 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12894 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12894 ⟨43,by decide⟩).lower ∧ (cell12894 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12894 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12894 ⟨44,by decide⟩).lower ∧ (cell12894 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12894 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12894 ⟨45,by decide⟩).lower ∧ (cell12894 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12894 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12894 ⟨46,by decide⟩).lower ∧ (cell12894 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12894 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12894 ⟨47,by decide⟩).lower ∧ (cell12894 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12894 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12894 ⟨48,by decide⟩).lower ∧ (cell12894 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12894 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12894 ⟨49,by decide⟩).lower ∧ (cell12894 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12894 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12894 ⟨50,by decide⟩).lower ∧ (cell12894 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12894 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12894 ⟨51,by decide⟩).lower ∧ (cell12894 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12894 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12894 ⟨52,by decide⟩).lower ∧ (cell12894 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12894 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12894 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12894 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12894,cell12894,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12894 i).lower ∧
    (cell12894 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12894 i).upper ≤ (0.532 : ℝ) ∧
    (cell12894 i).centre ≤ (0.1 : ℝ) ∧ (cell12894 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12894 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12894 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12894

/-! The local source numeric instances at 12894 have no network premises. -/
namespace BstLean.Part269.N12894
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12894)
open BstLean.Part268 (cell12894)

noncomputable def sourceNumerics12894 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12894 (cell12894 i)
      scalarRow12894.M scalarRow12894.H scalarRow12894.xi := by
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
    energy_allowance := scalarRow12894.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12894]
    centre_nonneg := (scalarRow12894.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12894])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12894
/-! Actual 12895 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12895
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12895 ≤ (1.035535061190 : ℝ) := by
  have hr : (113.556153510058 : ℝ) ≤ √(12895 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.556153510058 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12895 12895 (11 / 1000) ≤
    (0.008417747026 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12895) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.556153510058 : ℝ) ≤ √(12895 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12895)
  have hdiv : K / √(12895 : ℝ) ≤ K / 113.556153510058 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.556153510058 ≤ (0.008417747026 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12895.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12895 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12895 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12895 := gPlus_lower 12895
end BstLean.Part269.N12895

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12895
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035535061189 : ℝ) ≤ wn 12895 := by
  have hn : √(12895 : ℝ) ≤ 113.556153510059 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12895 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.556153510059 ≤ 2 / √(12895 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248006231 : ℝ) ≤ rhoBar 12895 BstLean.Part154.csC ∧
    rhoBar 12895 BstLean.Part154.csC ≤ 0.000248006615 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035535061189 : ℝ) / (1.295212 * 12895) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035535061190 : ℝ) / (1.29521 * 12895) := by gcongr
      _ ≤ (0.000248006615 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12895 BstLean.Part154.csC) ≤ 0.000992087968 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12895 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12895 BstLean.Part154.csC) (piBar (rhoBar 12895 BstLean.Part154.csC)) ≤ 0.000189428990 ∧
    cc1 (rhoBar 12895 BstLean.Part154.csC) (piBar (rhoBar 12895 BstLean.Part154.csC)) ≤ 0.000120534952 ∧
    cc2 (rhoBar 12895 BstLean.Part154.csC) ≤ 0.000069971497 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12895 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12895 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12895 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12895 BstLean.Part154.csC * nuR (rhoBar 12895 BstLean.Part154.csC)) ≤ 0.000496028607 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248006615 : ℝ) * 0.000992087968 := by gcongr
      _ ≤ (0.000496028607 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12895 BstLean.Part154.csC) * nuR (rhoBar 12895 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000992087968 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12895 BstLean.Part154.csC) * rhoBar 12895 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248006615 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248006615 / 2 + 0.399 * 0.000992087968 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189428990 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496028607 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120534952 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248006615 / 1.414213562 := by gcongr
      _ ≤ (0.000069971497 : ℝ) := by norm_num

end BstLean.Part269.N12895

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12895
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12895 BstLean.Part154.csC) (piBar (rhoBar 12895 BstLean.Part154.csC)) ≤ 1.54963E-7 := by
  have hr0 : 0 ≤ rhoBar 12895 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12895 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12895 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12895 BstLean.Part154.csC) (piBar (rhoBar 12895 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12895 BstLean.Part154.csC) (piBar (rhoBar 12895 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12895 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189428990 : ℝ) ^ 2 + 0.000120534952 ^ 2 + 3 * 0.000069971497 ^ 2 +
        2 * 0.797885 * 0.000189428990 * 0.000120534952 + 2 * 0.000189428990 * 0.000069971497 +
        4 * 0.797885 * 0.000120534952 * 0.000069971497 := by gcongr
    _ ≤ (1.54963E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12895 BstLean.Part154.csC Θ ≤ 0.002588154645 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12895 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12895 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12895 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12895 BstLean.Part154.csC) (piBar (rhoBar 12895 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12895 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035535061190 * 1.54963E-7 / (0.000248006231 : ℝ) := by gcongr
    _ ≤ 0.002588154645 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12895 BstLean.Part154.csC Θ ≤ 0.002870937973 + 0.000653985738 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12895 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12895 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12895 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035535061190 : ℝ) * ((2 * Θ * 0.000248006615 +
        (6863 / 10000) * 0.000248006615 * 12895 * 0.000992087968) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002870937973 + 0.000653985738 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12895 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12895 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12895 0.011 Θ ∧ gammaRatio 12895 0.011 Θ ≤ 0.000085258261 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12895 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035535061190 : ℝ) * 0.525 / ((1 - 0.011) * 12895) := by gcongr
      _ ≤ (0.000085258261 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12895 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12895 0.011 Θ) :=
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
    badAllowance 12895 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12895 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12895 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12895 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12895 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12895 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12895 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12895 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12895 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12895 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12895 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035535061190 : ℝ) * 12895 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12895 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003333974028 + 0.003242140383 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12895

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12895
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12895 BstLean.Part154.csC) (piBar (rhoBar 12895 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12895 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12895 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12895 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12895 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12895 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12895 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12895 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12895 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12895 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12895 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12895 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12895 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12895 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12895 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052081676812 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12895) ≤ 0.010516713927 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12895 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035535061190)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010516713927 + 2 * 0.737676 / 12895) := by gcongr
    _ ≤ (0.052081676812 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12895 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12895

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12895
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512253416 : ℝ) ≤ plow 12895 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12895) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052542697730)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358781189) : eMP 12895 0.011 xi bn ≤ 0.001170043308 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12895 : ℝ) * (1 - 0.011))) ≤ 0.000578550009 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001358781189 / (12895 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578550009 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578550009 : ℝ) + 3.141593 * 0.052542697730 / (12895 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001170043308 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052542697730)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358781189) : PiBarMP 12895 12 0.011 xi bn ≤ 0.160014852827 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12895 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036861649299 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.929867617030 : ℝ) ≤ √((12895 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.556153510058 : ℝ) ≤ √(12895 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12895) ≤ 0.122691794607 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036861649299 + 0.052542697730 * 1.772454 / (2 * (112.929867617030 : ℝ))) * (1 + 0.001170043308) +
        8 / (12895 * 113.556153510058) + 0.122691794607 := by gcongr
    _ ≤ (0.160014852827 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052542697730)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358781189) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281303616709) :
    parallelOracle 12895 0.011 xi bn cd ≤ 0.160990070672 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12895 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12895 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512253416 : ℝ) ≤ plow 12895 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.556153510058 : ℝ) ≤ √(12895 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281303616709 : ℝ) / (2 * 0.560512253416 * 113.556153510058)) * 0.160014852827 +
        0.281303616709 ^ 2 / (2 * 0.560512253416 * 113.556153510058) := by gcongr
    _ ≤ (0.160990070672 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052542697730) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358781189)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281303616709) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12895 12895 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512253416 : ℝ) ≤ plow 12895 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.556153510058 : ℝ) ≤ √(12895 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12895 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12895 Θ 1.22 ≤ 0.011677927255 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.556153510058 := by gcongr <;> linarith
      _ ≤ (0.011677927255 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12895 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12895 12895 0.011 ≤ 0.008417747026 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12895 12895 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12895 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12895 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12895 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12895 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160990070672 + 0.011677927255 + (0.008417747026 : ℝ) *
        (1 + 2 * (0.281303616709 + 0.011677927255) / (0.560512253416 * 113.556153510058))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12895]

end BstLean.Part269.N12895

/-! The original eight local profiles supply actual 12895 moment certificates. -/
namespace BstLean.Part269.N12895
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12895 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12895 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12895 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052542697730 ∧
    0 ≤ bN 12895 BstLean.Part154.csC (groupTheta g) ∧ bN 12895 BstLean.Part154.csC (groupTheta g) ≤ 0.001358781189 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12895 12895 0.011
      (momentAllowance 12895 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12895 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12895 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12895 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12895 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12895 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229221939897 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12895 0.011
      (momentAllowance 12895 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12895 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12895
/-! The actual computed-centre upper energy formula at 12895. -/
namespace BstLean.Part269.N12895
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12895

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12895
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12895)
open BstLean.Part268 (cell12895)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084940911487
  | 2 => 0.085873991948
  | 3 => 0.086803871086
  | 4 => 0.087731653411
  | 5 => 0.088658684450
  | 6 => 0.089586587750
  | 7 => 0.090517305594
  | 8 => 0.091453143505
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12895 12895 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12895 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003338665865 + 0.003247348463 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S21.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12895

/-! Actual upper energy certificates on all 43 source endpoints at 12895. -/
namespace BstLean.Part269.N12895
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12895)
open BstLean.Part268 (cell12895)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12895 (gMinus 12895) (1 - (cell12895 i).lower) ≤ 1 ∧
    energyUpper 12895 (gMinus 12895) (BstLean.Part211.gPlus 12895)
      (finiteEnergy 12895 12895 0.011) (1 - (cell12895 i).lower) ≤
      (cell12895 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨10,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨11,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨12,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨13,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨14,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨15,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨16,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨17,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨18,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨19,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨20,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨21,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨22,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨23,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨24,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨25,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨26,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨27,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨28,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨29,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨30,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨31,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨32,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨33,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨34,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨35,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨36,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨37,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨38,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨39,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨40,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨41,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨42,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨43,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨44,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨45,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨46,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨47,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨48,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨49,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨50,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨51,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12895) (by norm_num)
        (q := 1 - (cell12895 ⟨52,by decide⟩).lower)
        (by norm_num [cell12895]) (by norm_num [cell12895])
      exact ⟨E.1,E.2.trans (by norm_num [cell12895])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12895

/-! Source-cell containment and simple scalar guards at 12895. -/
namespace BstLean.Part269.N12895
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12895)
open BstLean.Part268 (cell12895)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12895 ⟨10,by decide⟩).lower ∧ (cell12895 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12895 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12895 ⟨11,by decide⟩).lower ∧ (cell12895 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12895 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12895 ⟨12,by decide⟩).lower ∧ (cell12895 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12895 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12895 ⟨13,by decide⟩).lower ∧ (cell12895 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12895 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12895 ⟨14,by decide⟩).lower ∧ (cell12895 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12895 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12895 ⟨15,by decide⟩).lower ∧ (cell12895 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12895 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12895 ⟨16,by decide⟩).lower ∧ (cell12895 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12895 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12895 ⟨17,by decide⟩).lower ∧ (cell12895 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12895 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12895 ⟨18,by decide⟩).lower ∧ (cell12895 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12895 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12895 ⟨19,by decide⟩).lower ∧ (cell12895 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12895 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12895 ⟨20,by decide⟩).lower ∧ (cell12895 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12895 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12895 ⟨21,by decide⟩).lower ∧ (cell12895 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12895 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12895 ⟨22,by decide⟩).lower ∧ (cell12895 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12895 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12895 ⟨23,by decide⟩).lower ∧ (cell12895 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12895 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12895 ⟨24,by decide⟩).lower ∧ (cell12895 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12895 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12895 ⟨25,by decide⟩).lower ∧ (cell12895 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12895 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12895 ⟨26,by decide⟩).lower ∧ (cell12895 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12895 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12895 ⟨27,by decide⟩).lower ∧ (cell12895 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12895 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12895 ⟨28,by decide⟩).lower ∧ (cell12895 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12895 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12895 ⟨29,by decide⟩).lower ∧ (cell12895 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12895 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12895 ⟨30,by decide⟩).lower ∧ (cell12895 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12895 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12895 ⟨31,by decide⟩).lower ∧ (cell12895 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12895 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12895 ⟨32,by decide⟩).lower ∧ (cell12895 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12895 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12895 ⟨33,by decide⟩).lower ∧ (cell12895 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12895 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12895 ⟨34,by decide⟩).lower ∧ (cell12895 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12895 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12895 ⟨35,by decide⟩).lower ∧ (cell12895 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12895 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12895 ⟨36,by decide⟩).lower ∧ (cell12895 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12895 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12895 ⟨37,by decide⟩).lower ∧ (cell12895 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12895 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12895 ⟨38,by decide⟩).lower ∧ (cell12895 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12895 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12895 ⟨39,by decide⟩).lower ∧ (cell12895 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12895 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12895 ⟨40,by decide⟩).lower ∧ (cell12895 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12895 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12895 ⟨41,by decide⟩).lower ∧ (cell12895 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12895 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12895 ⟨42,by decide⟩).lower ∧ (cell12895 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12895 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12895 ⟨43,by decide⟩).lower ∧ (cell12895 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12895 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12895 ⟨44,by decide⟩).lower ∧ (cell12895 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12895 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12895 ⟨45,by decide⟩).lower ∧ (cell12895 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12895 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12895 ⟨46,by decide⟩).lower ∧ (cell12895 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12895 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12895 ⟨47,by decide⟩).lower ∧ (cell12895 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12895 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12895 ⟨48,by decide⟩).lower ∧ (cell12895 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12895 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12895 ⟨49,by decide⟩).lower ∧ (cell12895 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12895 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12895 ⟨50,by decide⟩).lower ∧ (cell12895 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12895 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12895 ⟨51,by decide⟩).lower ∧ (cell12895 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12895 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12895 ⟨52,by decide⟩).lower ∧ (cell12895 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12895 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12895 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12895 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12895,cell12895,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12895 i).lower ∧
    (cell12895 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12895 i).upper ≤ (0.532 : ℝ) ∧
    (cell12895 i).centre ≤ (0.1 : ℝ) ∧ (cell12895 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12895 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12895 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12895

/-! The local source numeric instances at 12895 have no network premises. -/
namespace BstLean.Part269.N12895
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12895)
open BstLean.Part268 (cell12895)

noncomputable def sourceNumerics12895 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12895 (cell12895 i)
      scalarRow12895.M scalarRow12895.H scalarRow12895.xi := by
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
    energy_allowance := scalarRow12895.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12895]
    centre_nonneg := (scalarRow12895.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12895])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12895
/-! Actual 12896 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12896
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12896 ≤ (1.035533671382 : ℝ) := by
  have hr : (113.560556532627 : ℝ) ≤ √(12896 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.560556532627 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12896 12896 (11 / 1000) ≤
    (0.008417420647 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12896) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.560556532627 : ℝ) ≤ √(12896 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12896)
  have hdiv : K / √(12896 : ℝ) ≤ K / 113.560556532627 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.560556532627 ≤ (0.008417420647 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12896.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12896 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12896 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12896 := gPlus_lower 12896
end BstLean.Part269.N12896

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12896
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035533671381 : ℝ) ≤ wn 12896 := by
  have hn : √(12896 : ℝ) ≤ 113.560556532628 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12896 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.560556532628 ≤ 2 / √(12896 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247986667 : ℝ) ≤ rhoBar 12896 BstLean.Part154.csC ∧
    rhoBar 12896 BstLean.Part154.csC ≤ 0.000247987051 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035533671381 : ℝ) / (1.295212 * 12896) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035533671382 : ℝ) / (1.29521 * 12896) := by gcongr
      _ ≤ (0.000247987051 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12896 BstLean.Part154.csC) ≤ 0.000992009702 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12896 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12896 BstLean.Part154.csC) (piBar (rhoBar 12896 BstLean.Part154.csC)) ≤ 0.000189414046 ∧
    cc1 (rhoBar 12896 BstLean.Part154.csC) (piBar (rhoBar 12896 BstLean.Part154.csC)) ≤ 0.000120525443 ∧
    cc2 (rhoBar 12896 BstLean.Part154.csC) ≤ 0.000069965977 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12896 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12896 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12896 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12896 BstLean.Part154.csC * nuR (rhoBar 12896 BstLean.Part154.csC)) ≤ 0.000495989477 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247987051 : ℝ) * 0.000992009702 := by gcongr
      _ ≤ (0.000495989477 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12896 BstLean.Part154.csC) * nuR (rhoBar 12896 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000992009702 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12896 BstLean.Part154.csC) * rhoBar 12896 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247987051 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247987051 / 2 + 0.399 * 0.000992009702 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189414046 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495989477 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120525443 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247987051 / 1.414213562 := by gcongr
      _ ≤ (0.000069965977 : ℝ) := by norm_num

end BstLean.Part269.N12896

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12896
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12896 BstLean.Part154.csC) (piBar (rhoBar 12896 BstLean.Part154.csC)) ≤ 1.54939E-7 := by
  have hr0 : 0 ≤ rhoBar 12896 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12896 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12896 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12896 BstLean.Part154.csC) (piBar (rhoBar 12896 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12896 BstLean.Part154.csC) (piBar (rhoBar 12896 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12896 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189414046 : ℝ) ^ 2 + 0.000120525443 ^ 2 + 3 * 0.000069965977 ^ 2 +
        2 * 0.797885 * 0.000189414046 * 0.000120525443 + 2 * 0.000189414046 * 0.000069965977 +
        4 * 0.797885 * 0.000120525443 * 0.000069965977 := by gcongr
    _ ≤ (1.54939E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12896 BstLean.Part154.csC Θ ≤ 0.002587954481 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12896 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12896 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12896 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12896 BstLean.Part154.csC) (piBar (rhoBar 12896 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12896 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035533671382 * 1.54939E-7 / (0.000247986667 : ℝ) := by gcongr
    _ ≤ 0.002587954481 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12896 BstLean.Part154.csC Θ ≤ 0.002870703780 + 0.000653933271 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12896 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12896 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12896 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035533671382 : ℝ) * ((2 * Θ * 0.000247987051 +
        (6863 / 10000) * 0.000247987051 * 12896 * 0.000992009702) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002870703780 + 0.000653933271 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12896 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12896 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12896 0.011 Θ ∧ gammaRatio 12896 0.011 Θ ≤ 0.000085251536 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12896 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035533671382 : ℝ) * 0.525 / ((1 - 0.011) * 12896) := by gcongr
      _ ≤ (0.000085251536 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12896 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12896 0.011 Θ) :=
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
    badAllowance 12896 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12896 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12896 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12896 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12896 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12896 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12896 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12896 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12896 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12896 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12896 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035533671382 : ℝ) * 12896 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12896 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003333739835 + 0.003241887752 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12896

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12896
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12896 BstLean.Part154.csC) (piBar (rhoBar 12896 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12896 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12896 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12896 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12896 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12896 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12896 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12896 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12896 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12896 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12896 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12896 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12896 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12896 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12896 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052079635746 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12896) ≤ 0.010516306168 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12896 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035533671382)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010516306168 + 2 * 0.737676 / 12896) := by gcongr
    _ ≤ (0.052079635746 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12896 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12896

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12896
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512297278 : ℝ) ≤ plow 12896 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12896) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052542330905)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358676103) : eMP 12896 0.011 xi bn ≤ 0.001169952606 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12896 : ℝ) * (1 - 0.011))) ≤ 0.000578505205 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001358676103 / (12896 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578505205 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578505205 : ℝ) + 3.141593 * 0.052542330905 / (12896 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001169952606 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052542330905)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358676103) : PiBarMP 12896 12 0.011 xi bn ≤ 0.160008645753 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12896 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036860223860 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.934246356010 : ℝ) ≤ √((12896 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.560556532627 : ℝ) ≤ √(12896 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12896) ≤ 0.122687037544 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036860223860 + 0.052542330905 * 1.772454 / (2 * (112.934246356010 : ℝ))) * (1 + 0.001169952606) +
        8 / (12896 * 113.560556532627) + 0.122687037544 := by gcongr
    _ ≤ (0.160008645753 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052542330905)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358676103) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281300775489) :
    parallelOracle 12896 0.011 xi bn cd ≤ 0.160983795866 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12896 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12896 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512297278 : ℝ) ≤ plow 12896 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.560556532627 : ℝ) ≤ √(12896 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281300775489 : ℝ) / (2 * 0.560512297278 * 113.560556532627)) * 0.160008645753 +
        0.281300775489 ^ 2 / (2 * 0.560512297278 * 113.560556532627) := by gcongr
    _ ≤ (0.160983795866 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052542330905) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358676103)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281300775489) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12896 12896 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512297278 : ℝ) ≤ plow 12896 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.560556532627 : ℝ) ≤ √(12896 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12896 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12896 Θ 1.22 ≤ 0.011677474473 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.560556532627 := by gcongr <;> linarith
      _ ≤ (0.011677474473 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12896 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12896 12896 0.011 ≤ 0.008417420647 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12896 12896 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12896 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12896 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12896 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12896 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160983795866 + 0.011677474473 + (0.008417420647 : ℝ) *
        (1 + 2 * (0.281300775489 + 0.011677474473) / (0.560512297278 * 113.560556532627))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12896]

end BstLean.Part269.N12896

/-! The original eight local profiles supply actual 12896 moment certificates. -/
namespace BstLean.Part269.N12896
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12896 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12896 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12896 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052542330905 ∧
    0 ≤ bN 12896 BstLean.Part154.csC (groupTheta g) ∧ bN 12896 BstLean.Part154.csC (groupTheta g) ≤ 0.001358676103 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12896 12896 0.011
      (momentAllowance 12896 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12896 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12896 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12896 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12896 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12896 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229221139743 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12896 0.011
      (momentAllowance 12896 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12896 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12896
/-! The actual computed-centre upper energy formula at 12896. -/
namespace BstLean.Part269.N12896
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12896

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12896
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12896)
open BstLean.Part268 (cell12896)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084938187777
  | 2 => 0.085871222345
  | 3 => 0.086801049582
  | 4 => 0.087728772570
  | 5 => 0.088655735147
  | 6 => 0.089583558878
  | 7 => 0.090514183737
  | 8 => 0.091449912567
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12896 12896 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12896 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003338665865 + 0.003247348463 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S21.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12896

/-! Actual upper energy certificates on all 43 source endpoints at 12896. -/
namespace BstLean.Part269.N12896
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12896)
open BstLean.Part268 (cell12896)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12896 (gMinus 12896) (1 - (cell12896 i).lower) ≤ 1 ∧
    energyUpper 12896 (gMinus 12896) (BstLean.Part211.gPlus 12896)
      (finiteEnergy 12896 12896 0.011) (1 - (cell12896 i).lower) ≤
      (cell12896 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨10,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨11,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨12,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨13,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨14,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨15,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨16,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨17,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨18,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨19,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨20,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨21,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨22,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨23,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨24,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨25,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨26,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨27,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨28,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨29,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨30,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨31,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨32,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨33,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨34,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨35,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨36,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨37,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨38,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨39,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨40,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨41,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨42,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨43,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨44,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨45,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨46,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨47,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨48,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨49,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨50,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨51,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12896) (by norm_num)
        (q := 1 - (cell12896 ⟨52,by decide⟩).lower)
        (by norm_num [cell12896]) (by norm_num [cell12896])
      exact ⟨E.1,E.2.trans (by norm_num [cell12896])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12896

/-! Source-cell containment and simple scalar guards at 12896. -/
namespace BstLean.Part269.N12896
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12896)
open BstLean.Part268 (cell12896)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12896 ⟨10,by decide⟩).lower ∧ (cell12896 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12896 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12896 ⟨11,by decide⟩).lower ∧ (cell12896 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12896 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12896 ⟨12,by decide⟩).lower ∧ (cell12896 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12896 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12896 ⟨13,by decide⟩).lower ∧ (cell12896 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12896 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12896 ⟨14,by decide⟩).lower ∧ (cell12896 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12896 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12896 ⟨15,by decide⟩).lower ∧ (cell12896 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12896 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12896 ⟨16,by decide⟩).lower ∧ (cell12896 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12896 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12896 ⟨17,by decide⟩).lower ∧ (cell12896 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12896 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12896 ⟨18,by decide⟩).lower ∧ (cell12896 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12896 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12896 ⟨19,by decide⟩).lower ∧ (cell12896 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12896 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12896 ⟨20,by decide⟩).lower ∧ (cell12896 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12896 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12896 ⟨21,by decide⟩).lower ∧ (cell12896 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12896 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12896 ⟨22,by decide⟩).lower ∧ (cell12896 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12896 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12896 ⟨23,by decide⟩).lower ∧ (cell12896 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12896 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12896 ⟨24,by decide⟩).lower ∧ (cell12896 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12896 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12896 ⟨25,by decide⟩).lower ∧ (cell12896 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12896 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12896 ⟨26,by decide⟩).lower ∧ (cell12896 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12896 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12896 ⟨27,by decide⟩).lower ∧ (cell12896 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12896 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12896 ⟨28,by decide⟩).lower ∧ (cell12896 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12896 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12896 ⟨29,by decide⟩).lower ∧ (cell12896 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12896 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12896 ⟨30,by decide⟩).lower ∧ (cell12896 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12896 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12896 ⟨31,by decide⟩).lower ∧ (cell12896 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12896 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12896 ⟨32,by decide⟩).lower ∧ (cell12896 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12896 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12896 ⟨33,by decide⟩).lower ∧ (cell12896 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12896 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12896 ⟨34,by decide⟩).lower ∧ (cell12896 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12896 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12896 ⟨35,by decide⟩).lower ∧ (cell12896 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12896 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12896 ⟨36,by decide⟩).lower ∧ (cell12896 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12896 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12896 ⟨37,by decide⟩).lower ∧ (cell12896 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12896 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12896 ⟨38,by decide⟩).lower ∧ (cell12896 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12896 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12896 ⟨39,by decide⟩).lower ∧ (cell12896 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12896 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12896 ⟨40,by decide⟩).lower ∧ (cell12896 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12896 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12896 ⟨41,by decide⟩).lower ∧ (cell12896 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12896 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12896 ⟨42,by decide⟩).lower ∧ (cell12896 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12896 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12896 ⟨43,by decide⟩).lower ∧ (cell12896 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12896 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12896 ⟨44,by decide⟩).lower ∧ (cell12896 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12896 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12896 ⟨45,by decide⟩).lower ∧ (cell12896 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12896 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12896 ⟨46,by decide⟩).lower ∧ (cell12896 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12896 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12896 ⟨47,by decide⟩).lower ∧ (cell12896 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12896 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12896 ⟨48,by decide⟩).lower ∧ (cell12896 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12896 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12896 ⟨49,by decide⟩).lower ∧ (cell12896 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12896 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12896 ⟨50,by decide⟩).lower ∧ (cell12896 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12896 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12896 ⟨51,by decide⟩).lower ∧ (cell12896 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12896 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12896 ⟨52,by decide⟩).lower ∧ (cell12896 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12896 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12896 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12896 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12896,cell12896,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12896 i).lower ∧
    (cell12896 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12896 i).upper ≤ (0.532 : ℝ) ∧
    (cell12896 i).centre ≤ (0.1 : ℝ) ∧ (cell12896 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12896 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12896 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12896

/-! The local source numeric instances at 12896 have no network premises. -/
namespace BstLean.Part269.N12896
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12896)
open BstLean.Part268 (cell12896)

noncomputable def sourceNumerics12896 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12896 (cell12896 i)
      scalarRow12896.M scalarRow12896.H scalarRow12896.xi := by
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
    energy_allowance := scalarRow12896.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12896]
    centre_nonneg := (scalarRow12896.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12896])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12896
/-! Actual 12897 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12897
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12897 ≤ (1.035532281736 : ℝ) := by
  have hr : (113.564959384486 : ℝ) ≤ √(12897 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.564959384486 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12897 12897 (11 / 1000) ≤
    (0.008417094306 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12897) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.564959384486 : ℝ) ≤ √(12897 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12897)
  have hdiv : K / √(12897 : ℝ) ≤ K / 113.564959384486 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.564959384486 ≤ (0.008417094306 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12897.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12897 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12897 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12897 := gPlus_lower 12897
end BstLean.Part269.N12897

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12897
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035532281735 : ℝ) ≤ wn 12897 := by
  have hn : √(12897 : ℝ) ≤ 113.564959384487 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12897 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.564959384487 ≤ 2 / √(12897 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247967106 : ℝ) ≤ rhoBar 12897 BstLean.Part154.csC ∧
    rhoBar 12897 BstLean.Part154.csC ≤ 0.000247967490 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035532281735 : ℝ) / (1.295212 * 12897) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035532281736 : ℝ) / (1.29521 * 12897) := by gcongr
      _ ≤ (0.000247967490 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12897 BstLean.Part154.csC) ≤ 0.000991931448 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12897 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12897 BstLean.Part154.csC) (piBar (rhoBar 12897 BstLean.Part154.csC)) ≤ 0.000189399105 ∧
    cc1 (rhoBar 12897 BstLean.Part154.csC) (piBar (rhoBar 12897 BstLean.Part154.csC)) ≤ 0.000120515936 ∧
    cc2 (rhoBar 12897 BstLean.Part154.csC) ≤ 0.000069960459 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12897 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12897 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12897 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12897 BstLean.Part154.csC * nuR (rhoBar 12897 BstLean.Part154.csC)) ≤ 0.000495950352 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247967490 : ℝ) * 0.000991931448 := by gcongr
      _ ≤ (0.000495950352 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12897 BstLean.Part154.csC) * nuR (rhoBar 12897 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000991931448 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12897 BstLean.Part154.csC) * rhoBar 12897 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247967490 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247967490 / 2 + 0.399 * 0.000991931448 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189399105 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495950352 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120515936 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247967490 / 1.414213562 := by gcongr
      _ ≤ (0.000069960459 : ℝ) := by norm_num

end BstLean.Part269.N12897

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12897
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12897 BstLean.Part154.csC) (piBar (rhoBar 12897 BstLean.Part154.csC)) ≤ 1.54914E-7 := by
  have hr0 : 0 ≤ rhoBar 12897 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12897 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12897 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12897 BstLean.Part154.csC) (piBar (rhoBar 12897 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12897 BstLean.Part154.csC) (piBar (rhoBar 12897 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12897 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189399105 : ℝ) ^ 2 + 0.000120515936 ^ 2 + 3 * 0.000069960459 ^ 2 +
        2 * 0.797885 * 0.000189399105 * 0.000120515936 + 2 * 0.000189399105 * 0.000069960459 +
        4 * 0.797885 * 0.000120515936 * 0.000069960459 := by gcongr
    _ ≤ (1.54914E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12897 BstLean.Part154.csC Θ ≤ 0.002587737551 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12897 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12897 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12897 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12897 BstLean.Part154.csC) (piBar (rhoBar 12897 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12897 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035532281736 * 1.54914E-7 / (0.000247967106 : ℝ) := by gcongr
    _ ≤ 0.002587737551 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12897 BstLean.Part154.csC Θ ≤ 0.002870469623 + 0.000653880812 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12897 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12897 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12897 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035532281736 : ℝ) * ((2 * Θ * 0.000247967490 +
        (6863 / 10000) * 0.000247967490 * 12897 * 0.000991931448) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002870469623 + 0.000653880812 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12897 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12897 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12897 0.011 Θ ∧ gammaRatio 12897 0.011 Θ ≤ 0.000085244811 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12897 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035532281736 : ℝ) * 0.525 / ((1 - 0.011) * 12897) := by gcongr
      _ ≤ (0.000085244811 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12897 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12897 0.011 Θ) :=
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
    badAllowance 12897 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12897 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12897 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12897 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12897 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12897 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12897 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12897 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12897 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12897 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12897 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035532281736 : ℝ) * 12897 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12897 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003333505678 + 0.003241618363 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12897

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12897
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12897 BstLean.Part154.csC) (piBar (rhoBar 12897 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12897 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12897 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12897 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12897 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12897 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12897 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12897 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12897 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12897 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12897 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12897 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12897 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12897 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12897 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052077594921 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12897) ≤ 0.010515898457 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12897 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035532281736)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010515898457 + 2 * 0.737676 / 12897) := by gcongr
    _ ≤ (0.052077594921 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12897 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12897

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12897
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512341133 : ℝ) ≤ plow 12897 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12897) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541955319)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358562215) : eMP 12897 0.011 xi bn ≤ 0.001169858164 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12897 : ℝ) * (1 - 0.011))) ≤ 0.000578458532 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001358562215 / (12897 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578458532 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578458532 : ℝ) + 3.141593 * 0.052541955319 / (12897 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001169858164 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541955319)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358562215) : PiBarMP 12897 12 0.011 xi bn ≤ 0.160002319431 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12897 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036858678965 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.938624925222 : ℝ) ≤ √((12897 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.564959384486 : ℝ) ≤ √(12897 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12897) ≤ 0.122682281034 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036858678965 + 0.052541955319 * 1.772454 / (2 * (112.938624925222 : ℝ))) * (1 + 0.001169858164) +
        8 / (12897 * 113.564959384486) + 0.122682281034 := by gcongr
    _ ≤ (0.160002319431 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541955319)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358562215) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281297915397) :
    parallelOracle 12897 0.011 xi bn cd ≤ 0.160977401450 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12897 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12897 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512341133 : ℝ) ≤ plow 12897 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.564959384486 : ℝ) ≤ √(12897 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281297915397 : ℝ) / (2 * 0.560512341133 * 113.564959384486)) * 0.160002319431 +
        0.281297915397 ^ 2 / (2 * 0.560512341133 * 113.564959384486) := by gcongr
    _ ≤ (0.160977401450 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541955319) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358562215)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281297915397) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12897 12897 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512341133 : ℝ) ≤ plow 12897 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.564959384486 : ℝ) ≤ √(12897 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12897 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12897 Θ 1.22 ≤ 0.011677021744 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.564959384486 := by gcongr <;> linarith
      _ ≤ (0.011677021744 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12897 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12897 12897 0.011 ≤ 0.008417094306 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12897 12897 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12897 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12897 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12897 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12897 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160977401450 + 0.011677021744 + (0.008417094306 : ℝ) *
        (1 + 2 * (0.281297915397 + 0.011677021744) / (0.560512341133 * 113.564959384486))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12897]

end BstLean.Part269.N12897

/-! The original eight local profiles supply actual 12897 moment certificates. -/
namespace BstLean.Part269.N12897
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12897 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12897 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12897 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052541955319 ∧
    0 ≤ bN 12897 BstLean.Part154.csC (groupTheta g) ∧ bN 12897 BstLean.Part154.csC (groupTheta g) ≤ 0.001358562215 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12897 12897 0.011
      (momentAllowance 12897 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12897 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12897 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12897 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12897 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12897 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229220320476 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12897 0.011
      (momentAllowance 12897 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12897 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12897
/-! The actual computed-centre upper energy formula at 12897. -/
namespace BstLean.Part269.N12897
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12897

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12897
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12897)
open BstLean.Part268 (cell12897)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084935464960
  | 2 => 0.085868453670
  | 3 => 0.086798229050
  | 4 => 0.087725892752
  | 5 => 0.088652786931
  | 6 => 0.089580531173
  | 7 => 0.090511063141
  | 8 => 0.091446683005
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12897 12897 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12897 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003338665865 + 0.003247348463 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S21.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12897

/-! Actual upper energy certificates on all 43 source endpoints at 12897. -/
namespace BstLean.Part269.N12897
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12897)
open BstLean.Part268 (cell12897)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12897 (gMinus 12897) (1 - (cell12897 i).lower) ≤ 1 ∧
    energyUpper 12897 (gMinus 12897) (BstLean.Part211.gPlus 12897)
      (finiteEnergy 12897 12897 0.011) (1 - (cell12897 i).lower) ≤
      (cell12897 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨10,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨11,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨12,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨13,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨14,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨15,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨16,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨17,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨18,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨19,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨20,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨21,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨22,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨23,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨24,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨25,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨26,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨27,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨28,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨29,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨30,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨31,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨32,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨33,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨34,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨35,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨36,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨37,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨38,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨39,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨40,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨41,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨42,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨43,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨44,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨45,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨46,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨47,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨48,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨49,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨50,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨51,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12897) (by norm_num)
        (q := 1 - (cell12897 ⟨52,by decide⟩).lower)
        (by norm_num [cell12897]) (by norm_num [cell12897])
      exact ⟨E.1,E.2.trans (by norm_num [cell12897])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12897

/-! Source-cell containment and simple scalar guards at 12897. -/
namespace BstLean.Part269.N12897
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12897)
open BstLean.Part268 (cell12897)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12897 ⟨10,by decide⟩).lower ∧ (cell12897 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12897 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12897 ⟨11,by decide⟩).lower ∧ (cell12897 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12897 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12897 ⟨12,by decide⟩).lower ∧ (cell12897 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12897 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12897 ⟨13,by decide⟩).lower ∧ (cell12897 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12897 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12897 ⟨14,by decide⟩).lower ∧ (cell12897 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12897 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12897 ⟨15,by decide⟩).lower ∧ (cell12897 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12897 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12897 ⟨16,by decide⟩).lower ∧ (cell12897 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12897 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12897 ⟨17,by decide⟩).lower ∧ (cell12897 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12897 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12897 ⟨18,by decide⟩).lower ∧ (cell12897 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12897 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12897 ⟨19,by decide⟩).lower ∧ (cell12897 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12897 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12897 ⟨20,by decide⟩).lower ∧ (cell12897 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12897 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12897 ⟨21,by decide⟩).lower ∧ (cell12897 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12897 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12897 ⟨22,by decide⟩).lower ∧ (cell12897 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12897 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12897 ⟨23,by decide⟩).lower ∧ (cell12897 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12897 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12897 ⟨24,by decide⟩).lower ∧ (cell12897 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12897 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12897 ⟨25,by decide⟩).lower ∧ (cell12897 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12897 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12897 ⟨26,by decide⟩).lower ∧ (cell12897 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12897 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12897 ⟨27,by decide⟩).lower ∧ (cell12897 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12897 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12897 ⟨28,by decide⟩).lower ∧ (cell12897 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12897 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12897 ⟨29,by decide⟩).lower ∧ (cell12897 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12897 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12897 ⟨30,by decide⟩).lower ∧ (cell12897 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12897 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12897 ⟨31,by decide⟩).lower ∧ (cell12897 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12897 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12897 ⟨32,by decide⟩).lower ∧ (cell12897 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12897 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12897 ⟨33,by decide⟩).lower ∧ (cell12897 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12897 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12897 ⟨34,by decide⟩).lower ∧ (cell12897 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12897 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12897 ⟨35,by decide⟩).lower ∧ (cell12897 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12897 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12897 ⟨36,by decide⟩).lower ∧ (cell12897 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12897 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12897 ⟨37,by decide⟩).lower ∧ (cell12897 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12897 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12897 ⟨38,by decide⟩).lower ∧ (cell12897 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12897 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12897 ⟨39,by decide⟩).lower ∧ (cell12897 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12897 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12897 ⟨40,by decide⟩).lower ∧ (cell12897 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12897 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12897 ⟨41,by decide⟩).lower ∧ (cell12897 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12897 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12897 ⟨42,by decide⟩).lower ∧ (cell12897 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12897 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12897 ⟨43,by decide⟩).lower ∧ (cell12897 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12897 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12897 ⟨44,by decide⟩).lower ∧ (cell12897 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12897 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12897 ⟨45,by decide⟩).lower ∧ (cell12897 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12897 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12897 ⟨46,by decide⟩).lower ∧ (cell12897 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12897 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12897 ⟨47,by decide⟩).lower ∧ (cell12897 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12897 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12897 ⟨48,by decide⟩).lower ∧ (cell12897 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12897 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12897 ⟨49,by decide⟩).lower ∧ (cell12897 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12897 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12897 ⟨50,by decide⟩).lower ∧ (cell12897 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12897 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12897 ⟨51,by decide⟩).lower ∧ (cell12897 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12897 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12897 ⟨52,by decide⟩).lower ∧ (cell12897 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12897 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12897 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12897 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12897,cell12897,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12897 i).lower ∧
    (cell12897 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12897 i).upper ≤ (0.532 : ℝ) ∧
    (cell12897 i).centre ≤ (0.1 : ℝ) ∧ (cell12897 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12897 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12897 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12897

/-! The local source numeric instances at 12897 have no network premises. -/
namespace BstLean.Part269.N12897
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12897)
open BstLean.Part268 (cell12897)

noncomputable def sourceNumerics12897 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12897 (cell12897 i)
      scalarRow12897.M scalarRow12897.H scalarRow12897.xi := by
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
    energy_allowance := scalarRow12897.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12897]
    centre_nonneg := (scalarRow12897.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12897])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12897
/-! Actual 12898 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12898
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12898 ≤ (1.035530892252 : ℝ) := by
  have hr : (113.569362065655 : ℝ) ≤ √(12898 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.569362065655 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12898 12898 (11 / 1000) ≤
    (0.008416768003 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12898) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.569362065655 : ℝ) ≤ √(12898 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12898)
  have hdiv : K / √(12898 : ℝ) ≤ K / 113.569362065655 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.569362065655 ≤ (0.008416768003 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12898.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12898 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12898 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12898 := gPlus_lower 12898
end BstLean.Part269.N12898

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12898
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035530892251 : ℝ) ≤ wn 12898 := by
  have hn : √(12898 : ℝ) ≤ 113.569362065656 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12898 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.569362065656 ≤ 2 / √(12898 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247947548 : ℝ) ≤ rhoBar 12898 BstLean.Part154.csC ∧
    rhoBar 12898 BstLean.Part154.csC ≤ 0.000247947932 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035530892251 : ℝ) / (1.295212 * 12898) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035530892252 : ℝ) / (1.29521 * 12898) := by gcongr
      _ ≤ (0.000247947932 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12898 BstLean.Part154.csC) ≤ 0.000991853207 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12898 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12898 BstLean.Part154.csC) (piBar (rhoBar 12898 BstLean.Part154.csC)) ≤ 0.000189384166 ∧
    cc1 (rhoBar 12898 BstLean.Part154.csC) (piBar (rhoBar 12898 BstLean.Part154.csC)) ≤ 0.000120506430 ∧
    cc2 (rhoBar 12898 BstLean.Part154.csC) ≤ 0.000069954940 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12898 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12898 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12898 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12898 BstLean.Part154.csC * nuR (rhoBar 12898 BstLean.Part154.csC)) ≤ 0.000495911234 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247947932 : ℝ) * 0.000991853207 := by gcongr
      _ ≤ (0.000495911234 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12898 BstLean.Part154.csC) * nuR (rhoBar 12898 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000991853207 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12898 BstLean.Part154.csC) * rhoBar 12898 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247947932 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247947932 / 2 + 0.399 * 0.000991853207 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189384166 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495911234 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120506430 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247947932 / 1.414213562 := by gcongr
      _ ≤ (0.000069954940 : ℝ) := by norm_num

end BstLean.Part269.N12898

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12898
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12898 BstLean.Part154.csC) (piBar (rhoBar 12898 BstLean.Part154.csC)) ≤ 1.54890E-7 := by
  have hr0 : 0 ≤ rhoBar 12898 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12898 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12898 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12898 BstLean.Part154.csC) (piBar (rhoBar 12898 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12898 BstLean.Part154.csC) (piBar (rhoBar 12898 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12898 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189384166 : ℝ) ^ 2 + 0.000120506430 ^ 2 + 3 * 0.000069954940 ^ 2 +
        2 * 0.797885 * 0.000189384166 * 0.000120506430 + 2 * 0.000189384166 * 0.000069954940 +
        4 * 0.797885 * 0.000120506430 * 0.000069954940 := by gcongr
    _ ≤ (1.54890E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12898 BstLean.Part154.csC Θ ≤ 0.002587537263 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12898 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12898 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12898 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12898 BstLean.Part154.csC) (piBar (rhoBar 12898 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12898 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035530892252 * 1.54890E-7 / (0.000247947548 : ℝ) := by gcongr
    _ ≤ 0.002587537263 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12898 BstLean.Part154.csC Θ ≤ 0.002870235504 + 0.000653828361 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12898 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12898 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12898 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035530892252 : ℝ) * ((2 * Θ * 0.000247947932 +
        (6863 / 10000) * 0.000247947932 * 12898 * 0.000991853207) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002870235504 + 0.000653828361 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12898 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12898 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12898 0.011 Θ ∧ gammaRatio 12898 0.011 Θ ≤ 0.000085238088 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12898 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035530892252 : ℝ) * 0.525 / ((1 - 0.011) * 12898) := by gcongr
      _ ≤ (0.000085238088 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12898 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12898 0.011 Θ) :=
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
    badAllowance 12898 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12898 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12898 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12898 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12898 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12898 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12898 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12898 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12898 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12898 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12898 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035530892252 : ℝ) * 12898 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12898 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003333271559 + 0.003241365624 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12898

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12898
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12898 BstLean.Part154.csC) (piBar (rhoBar 12898 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12898 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12898 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12898 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12898 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12898 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12898 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12898 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12898 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12898 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12898 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12898 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12898 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12898 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12898 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052075554328 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12898) ≤ 0.010515490792 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12898 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035530892252)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010515490792 + 2 * 0.737676 / 12898) := by gcongr
    _ ≤ (0.052075554328 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12898 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12898

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12898
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512384982 : ℝ) ≤ plow 12898 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12898) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541588512)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358457064) : eMP 12898 0.011 xi bn ≤ 0.001169767448 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12898 : ℝ) * (1 - 0.011))) ≤ 0.000578413721 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001358457064 / (12898 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578413721 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578413721 : ℝ) + 3.141593 * 0.052541588512 / (12898 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001169767448 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541588512)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358457064) : PiBarMP 12898 12 0.011 xi bn ≤ 0.159996112471 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12898 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036857252530 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.943003324685 : ℝ) ≤ √((12898 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.569362065655 : ℝ) ≤ √(12898 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12898) ≤ 0.122677525077 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036857252530 + 0.052541588512 * 1.772454 / (2 * (112.943003324685 : ℝ))) * (1 + 0.001169767448) +
        8 / (12898 * 113.569362065655) + 0.122677525077 := by gcongr
    _ ≤ (0.159996112471 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541588512)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358457064) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281295074684) :
    parallelOracle 12898 0.011 xi bn cd ≤ 0.160971126776 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12898 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12898 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512384982 : ℝ) ≤ plow 12898 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.569362065655 : ℝ) ≤ √(12898 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281295074684 : ℝ) / (2 * 0.560512384982 * 113.569362065655)) * 0.159996112471 +
        0.281295074684 ^ 2 / (2 * 0.560512384982 * 113.569362065655) := by gcongr
    _ ≤ (0.160971126776 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541588512) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358457064)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281295074684) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12898 12898 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512384982 : ℝ) ≤ plow 12898 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.569362065655 : ℝ) ≤ √(12898 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12898 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12898 Θ 1.22 ≤ 0.011676569067 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.569362065655 := by gcongr <;> linarith
      _ ≤ (0.011676569067 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12898 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12898 12898 0.011 ≤ 0.008416768003 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12898 12898 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12898 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12898 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12898 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12898 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160971126776 + 0.011676569067 + (0.008416768003 : ℝ) *
        (1 + 2 * (0.281295074684 + 0.011676569067) / (0.560512384982 * 113.569362065655))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12898]

end BstLean.Part269.N12898

/-! The original eight local profiles supply actual 12898 moment certificates. -/
namespace BstLean.Part269.N12898
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12898 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12898 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12898 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052541588512 ∧
    0 ≤ bN 12898 BstLean.Part154.csC (groupTheta g) ∧ bN 12898 BstLean.Part154.csC (groupTheta g) ≤ 0.001358457064 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12898 12898 0.011
      (momentAllowance 12898 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12898 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12898 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12898 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12898 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12898 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229219520356 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12898 0.011
      (momentAllowance 12898 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12898 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12898
/-! The actual computed-centre upper energy formula at 12898. -/
namespace BstLean.Part269.N12898
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12898

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12898
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12898)
open BstLean.Part268 (cell12898)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084932743036
  | 2 => 0.085865685923
  | 3 => 0.086795409487
  | 4 => 0.087723013957
  | 5 => 0.088649839802
  | 6 => 0.089577504632
  | 7 => 0.090507943805
  | 8 => 0.091443454817
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12898 12898 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12898 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003338665865 + 0.003247348463 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S21.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12898

/-! Actual upper energy certificates on all 43 source endpoints at 12898. -/
namespace BstLean.Part269.N12898
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12898)
open BstLean.Part268 (cell12898)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12898 (gMinus 12898) (1 - (cell12898 i).lower) ≤ 1 ∧
    energyUpper 12898 (gMinus 12898) (BstLean.Part211.gPlus 12898)
      (finiteEnergy 12898 12898 0.011) (1 - (cell12898 i).lower) ≤
      (cell12898 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨10,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨11,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨12,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨13,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨14,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨15,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨16,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨17,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨18,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨19,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨20,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨21,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨22,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨23,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨24,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨25,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨26,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨27,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨28,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨29,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨30,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨31,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨32,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨33,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨34,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨35,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨36,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨37,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨38,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨39,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨40,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨41,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨42,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨43,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨44,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨45,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨46,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨47,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨48,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨49,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨50,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨51,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12898) (by norm_num)
        (q := 1 - (cell12898 ⟨52,by decide⟩).lower)
        (by norm_num [cell12898]) (by norm_num [cell12898])
      exact ⟨E.1,E.2.trans (by norm_num [cell12898])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12898

/-! Source-cell containment and simple scalar guards at 12898. -/
namespace BstLean.Part269.N12898
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12898)
open BstLean.Part268 (cell12898)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12898 ⟨10,by decide⟩).lower ∧ (cell12898 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12898 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12898 ⟨11,by decide⟩).lower ∧ (cell12898 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12898 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12898 ⟨12,by decide⟩).lower ∧ (cell12898 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12898 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12898 ⟨13,by decide⟩).lower ∧ (cell12898 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12898 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12898 ⟨14,by decide⟩).lower ∧ (cell12898 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12898 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12898 ⟨15,by decide⟩).lower ∧ (cell12898 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12898 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12898 ⟨16,by decide⟩).lower ∧ (cell12898 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12898 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12898 ⟨17,by decide⟩).lower ∧ (cell12898 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12898 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12898 ⟨18,by decide⟩).lower ∧ (cell12898 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12898 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12898 ⟨19,by decide⟩).lower ∧ (cell12898 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12898 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12898 ⟨20,by decide⟩).lower ∧ (cell12898 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12898 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12898 ⟨21,by decide⟩).lower ∧ (cell12898 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12898 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12898 ⟨22,by decide⟩).lower ∧ (cell12898 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12898 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12898 ⟨23,by decide⟩).lower ∧ (cell12898 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12898 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12898 ⟨24,by decide⟩).lower ∧ (cell12898 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12898 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12898 ⟨25,by decide⟩).lower ∧ (cell12898 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12898 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12898 ⟨26,by decide⟩).lower ∧ (cell12898 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12898 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12898 ⟨27,by decide⟩).lower ∧ (cell12898 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12898 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12898 ⟨28,by decide⟩).lower ∧ (cell12898 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12898 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12898 ⟨29,by decide⟩).lower ∧ (cell12898 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12898 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12898 ⟨30,by decide⟩).lower ∧ (cell12898 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12898 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12898 ⟨31,by decide⟩).lower ∧ (cell12898 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12898 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12898 ⟨32,by decide⟩).lower ∧ (cell12898 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12898 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12898 ⟨33,by decide⟩).lower ∧ (cell12898 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12898 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12898 ⟨34,by decide⟩).lower ∧ (cell12898 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12898 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12898 ⟨35,by decide⟩).lower ∧ (cell12898 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12898 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12898 ⟨36,by decide⟩).lower ∧ (cell12898 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12898 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12898 ⟨37,by decide⟩).lower ∧ (cell12898 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12898 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12898 ⟨38,by decide⟩).lower ∧ (cell12898 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12898 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12898 ⟨39,by decide⟩).lower ∧ (cell12898 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12898 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12898 ⟨40,by decide⟩).lower ∧ (cell12898 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12898 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12898 ⟨41,by decide⟩).lower ∧ (cell12898 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12898 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12898 ⟨42,by decide⟩).lower ∧ (cell12898 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12898 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12898 ⟨43,by decide⟩).lower ∧ (cell12898 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12898 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12898 ⟨44,by decide⟩).lower ∧ (cell12898 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12898 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12898 ⟨45,by decide⟩).lower ∧ (cell12898 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12898 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12898 ⟨46,by decide⟩).lower ∧ (cell12898 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12898 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12898 ⟨47,by decide⟩).lower ∧ (cell12898 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12898 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12898 ⟨48,by decide⟩).lower ∧ (cell12898 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12898 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12898 ⟨49,by decide⟩).lower ∧ (cell12898 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12898 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12898 ⟨50,by decide⟩).lower ∧ (cell12898 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12898 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12898 ⟨51,by decide⟩).lower ∧ (cell12898 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12898 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12898 ⟨52,by decide⟩).lower ∧ (cell12898 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12898 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12898 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12898 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12898,cell12898,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12898 i).lower ∧
    (cell12898 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12898 i).upper ≤ (0.532 : ℝ) ∧
    (cell12898 i).centre ≤ (0.1 : ℝ) ∧ (cell12898 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12898 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12898 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12898

/-! The local source numeric instances at 12898 have no network premises. -/
namespace BstLean.Part269.N12898
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12898)
open BstLean.Part268 (cell12898)

noncomputable def sourceNumerics12898 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12898 (cell12898 i)
      scalarRow12898.M scalarRow12898.H scalarRow12898.xi := by
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
    energy_allowance := scalarRow12898.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12898]
    centre_nonneg := (scalarRow12898.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12898])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12898
/-! Actual 12899 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12899
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12899 ≤ (1.035529502931 : ℝ) := by
  have hr : (113.573764576155 : ℝ) ≤ √(12899 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.573764576155 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12899 12899 (11 / 1000) ≤
    (0.008416441737 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12899) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.573764576155 : ℝ) ≤ √(12899 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12899)
  have hdiv : K / √(12899 : ℝ) ≤ K / 113.573764576155 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.573764576155 ≤ (0.008416441737 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12899.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12899 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12899 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12899 := gPlus_lower 12899
end BstLean.Part269.N12899

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12899
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035529502930 : ℝ) ≤ wn 12899 := by
  have hn : √(12899 : ℝ) ≤ 113.573764576156 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12899 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.573764576156 ≤ 2 / √(12899 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000247927993 : ℝ) ≤ rhoBar 12899 BstLean.Part154.csC ∧
    rhoBar 12899 BstLean.Part154.csC ≤ 0.000247928377 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035529502930 : ℝ) / (1.295212 * 12899) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035529502931 : ℝ) / (1.29521 * 12899) := by gcongr
      _ ≤ (0.000247928377 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12899 BstLean.Part154.csC) ≤ 0.000991774977 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12899 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12899 BstLean.Part154.csC) (piBar (rhoBar 12899 BstLean.Part154.csC)) ≤ 0.000189369229 ∧
    cc1 (rhoBar 12899 BstLean.Part154.csC) (piBar (rhoBar 12899 BstLean.Part154.csC)) ≤ 0.000120496926 ∧
    cc2 (rhoBar 12899 BstLean.Part154.csC) ≤ 0.000069949423 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12899 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12899 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12899 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12899 BstLean.Part154.csC * nuR (rhoBar 12899 BstLean.Part154.csC)) ≤ 0.000495872122 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000247928377 : ℝ) * 0.000991774977 := by gcongr
      _ ≤ (0.000495872122 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12899 BstLean.Part154.csC) * nuR (rhoBar 12899 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000991774977 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12899 BstLean.Part154.csC) * rhoBar 12899 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000247928377 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000247928377 / 2 + 0.399 * 0.000991774977 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189369229 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000495872122 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120496926 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000247928377 / 1.414213562 := by gcongr
      _ ≤ (0.000069949423 : ℝ) := by norm_num

end BstLean.Part269.N12899

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12899
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12899 BstLean.Part154.csC) (piBar (rhoBar 12899 BstLean.Part154.csC)) ≤ 1.54865E-7 := by
  have hr0 : 0 ≤ rhoBar 12899 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12899 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12899 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12899 BstLean.Part154.csC) (piBar (rhoBar 12899 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12899 BstLean.Part154.csC) (piBar (rhoBar 12899 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12899 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189369229 : ℝ) ^ 2 + 0.000120496926 ^ 2 + 3 * 0.000069949423 ^ 2 +
        2 * 0.797885 * 0.000189369229 * 0.000120496926 + 2 * 0.000189369229 * 0.000069949423 +
        4 * 0.797885 * 0.000120496926 * 0.000069949423 := by gcongr
    _ ≤ (1.54865E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12899 BstLean.Part154.csC Θ ≤ 0.002587320206 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12899 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12899 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12899 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12899 BstLean.Part154.csC) (piBar (rhoBar 12899 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12899 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035529502931 * 1.54865E-7 / (0.000247927993 : ℝ) := by gcongr
    _ ≤ 0.002587320206 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12899 BstLean.Part154.csC Θ ≤ 0.002870001419 + 0.000653775918 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12899 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12899 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12899 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035529502931 : ℝ) * ((2 * Θ * 0.000247928377 +
        (6863 / 10000) * 0.000247928377 * 12899 * 0.000991774977) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002870001419 + 0.000653775918 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12899 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12899 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12899 0.011 Θ ∧ gammaRatio 12899 0.011 Θ ≤ 0.000085231365 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12899 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035529502931 : ℝ) * 0.525 / ((1 - 0.011) * 12899) := by gcongr
      _ ≤ (0.000085231365 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12899 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12899 0.011 Θ) :=
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
    badAllowance 12899 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12899 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12899 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12899 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12899 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12899 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12899 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12899 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12899 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12899 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12899 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035529502931 : ℝ) * 12899 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12899 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003333037474 + 0.003241096124 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12899

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12899
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12899 BstLean.Part154.csC) (piBar (rhoBar 12899 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12899 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12899 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12899 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12899 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12899 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12899 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12899 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12899 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12899 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12899 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12899 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12899 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12899 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12899 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052073513982 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12899) ≤ 0.010515083176 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12899 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035529502931)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010515083176 + 2 * 0.737676 / 12899) := by gcongr
    _ ≤ (0.052073513982 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12899 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12899

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12899
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560512428823 : ℝ) ≤ plow 12899 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12899) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541212940)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358343109) : eMP 12899 0.011 xi bn ≤ 0.001169672990 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12899 : ℝ) * (1 - 0.011))) ≤ 0.000578367040 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001358343109 / (12899 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578367040 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578367040 : ℝ) + 3.141593 * 0.052541212940 / (12899 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001169672990 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541212940)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358343109) : PiBarMP 12899 12 0.011 xi bn ≤ 0.159989786225 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12899 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036855706601 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.947381554421 : ℝ) ≤ √((12899 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.573764576155 : ℝ) ≤ √(12899 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12899) ≤ 0.122672769674 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036855706601 + 0.052541212940 * 1.772454 / (2 * (112.947381554421 : ℝ))) * (1 + 0.001169672990) +
        8 / (12899 * 113.573764576155) + 0.122672769674 := by gcongr
    _ ≤ (0.159989786225 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541212940)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358343109) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281292215096) :
    parallelOracle 12899 0.011 xi bn cd ≤ 0.160964732453 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12899 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12899 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560512428823 : ℝ) ≤ plow 12899 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.573764576155 : ℝ) ≤ √(12899 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281292215096 : ℝ) / (2 * 0.560512428823 * 113.573764576155)) * 0.159989786225 +
        0.281292215096 ^ 2 / (2 * 0.560512428823 * 113.573764576155) := by gcongr
    _ ≤ (0.160964732453 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052541212940) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001358343109)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281292215096) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12899 12899 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560512428823 : ℝ) ≤ plow 12899 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.573764576155 : ℝ) ≤ √(12899 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12899 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12899 Θ 1.22 ≤ 0.011676116443 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.573764576155 := by gcongr <;> linarith
      _ ≤ (0.011676116443 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12899 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12899 12899 0.011 ≤ 0.008416441737 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12899 12899 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12899 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12899 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12899 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12899 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.160964732453 + 0.011676116443 + (0.008416441737 : ℝ) *
        (1 + 2 * (0.281292215096 + 0.011676116443) / (0.560512428823 * 113.573764576155))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12899]

end BstLean.Part269.N12899

/-! The original eight local profiles supply actual 12899 moment certificates. -/
namespace BstLean.Part269.N12899
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12899 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12899 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12899 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052541212940 ∧
    0 ≤ bN 12899 BstLean.Part154.csC (groupTheta g) ∧ bN 12899 BstLean.Part154.csC (groupTheta g) ≤ 0.001358343109 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12899 12899 0.011
      (momentAllowance 12899 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12899 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12899 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12899 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12899 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12899 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229218701114 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12899 0.011
      (momentAllowance 12899 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12899 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12899
/-! The actual computed-centre upper energy formula at 12899. -/
namespace BstLean.Part269.N12899
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12899

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12899
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12899)
open BstLean.Part268 (cell12899)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084930022003
  | 2 => 0.085862919102
  | 3 => 0.086792590893
  | 4 => 0.087720136183
  | 5 => 0.088646893759
  | 6 => 0.089574479255
  | 7 => 0.090504825728
  | 8 => 0.091440228002
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12899 12899 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12899 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003338665865 + 0.003247348463 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S21.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S21.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12899

/-! Actual upper energy certificates on all 43 source endpoints at 12899. -/
namespace BstLean.Part269.N12899
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12899)
open BstLean.Part268 (cell12899)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12899 (gMinus 12899) (1 - (cell12899 i).lower) ≤ 1 ∧
    energyUpper 12899 (gMinus 12899) (BstLean.Part211.gPlus 12899)
      (finiteEnergy 12899 12899 0.011) (1 - (cell12899 i).lower) ≤
      (cell12899 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨10,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨11,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨12,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨13,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨14,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨15,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨16,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨17,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨18,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨19,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨20,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨21,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨22,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨23,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨24,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨25,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨26,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨27,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨28,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨29,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨30,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨31,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨32,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨33,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨34,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨35,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨36,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨37,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨38,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨39,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨40,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨41,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨42,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨43,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨44,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨45,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨46,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨47,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨48,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨49,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨50,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨51,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12899) (by norm_num)
        (q := 1 - (cell12899 ⟨52,by decide⟩).lower)
        (by norm_num [cell12899]) (by norm_num [cell12899])
      exact ⟨E.1,E.2.trans (by norm_num [cell12899])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12899

/-! Source-cell containment and simple scalar guards at 12899. -/
namespace BstLean.Part269.N12899
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12899)
open BstLean.Part268 (cell12899)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12899 ⟨10,by decide⟩).lower ∧ (cell12899 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12899 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12899 ⟨11,by decide⟩).lower ∧ (cell12899 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12899 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12899 ⟨12,by decide⟩).lower ∧ (cell12899 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12899 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12899 ⟨13,by decide⟩).lower ∧ (cell12899 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12899 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12899 ⟨14,by decide⟩).lower ∧ (cell12899 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12899 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12899 ⟨15,by decide⟩).lower ∧ (cell12899 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12899 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12899 ⟨16,by decide⟩).lower ∧ (cell12899 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12899 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12899 ⟨17,by decide⟩).lower ∧ (cell12899 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12899 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12899 ⟨18,by decide⟩).lower ∧ (cell12899 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12899 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12899 ⟨19,by decide⟩).lower ∧ (cell12899 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12899 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12899 ⟨20,by decide⟩).lower ∧ (cell12899 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12899 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12899 ⟨21,by decide⟩).lower ∧ (cell12899 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12899 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12899 ⟨22,by decide⟩).lower ∧ (cell12899 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12899 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12899 ⟨23,by decide⟩).lower ∧ (cell12899 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12899 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12899 ⟨24,by decide⟩).lower ∧ (cell12899 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12899 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12899 ⟨25,by decide⟩).lower ∧ (cell12899 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12899 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12899 ⟨26,by decide⟩).lower ∧ (cell12899 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12899 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12899 ⟨27,by decide⟩).lower ∧ (cell12899 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12899 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12899 ⟨28,by decide⟩).lower ∧ (cell12899 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12899 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12899 ⟨29,by decide⟩).lower ∧ (cell12899 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12899 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12899 ⟨30,by decide⟩).lower ∧ (cell12899 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12899 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12899 ⟨31,by decide⟩).lower ∧ (cell12899 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12899 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12899 ⟨32,by decide⟩).lower ∧ (cell12899 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12899 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12899 ⟨33,by decide⟩).lower ∧ (cell12899 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12899 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12899 ⟨34,by decide⟩).lower ∧ (cell12899 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12899 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12899 ⟨35,by decide⟩).lower ∧ (cell12899 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12899 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12899 ⟨36,by decide⟩).lower ∧ (cell12899 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12899 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12899 ⟨37,by decide⟩).lower ∧ (cell12899 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12899 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12899 ⟨38,by decide⟩).lower ∧ (cell12899 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12899 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12899 ⟨39,by decide⟩).lower ∧ (cell12899 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12899 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12899 ⟨40,by decide⟩).lower ∧ (cell12899 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12899 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12899 ⟨41,by decide⟩).lower ∧ (cell12899 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12899 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12899 ⟨42,by decide⟩).lower ∧ (cell12899 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12899 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12899 ⟨43,by decide⟩).lower ∧ (cell12899 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12899 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12899 ⟨44,by decide⟩).lower ∧ (cell12899 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12899 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12899 ⟨45,by decide⟩).lower ∧ (cell12899 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12899 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12899 ⟨46,by decide⟩).lower ∧ (cell12899 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12899 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12899 ⟨47,by decide⟩).lower ∧ (cell12899 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12899 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12899 ⟨48,by decide⟩).lower ∧ (cell12899 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12899 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12899 ⟨49,by decide⟩).lower ∧ (cell12899 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12899 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12899 ⟨50,by decide⟩).lower ∧ (cell12899 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12899 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12899 ⟨51,by decide⟩).lower ∧ (cell12899 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12899 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12899 ⟨52,by decide⟩).lower ∧ (cell12899 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12899 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12899 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12899 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12899,cell12899,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12899 i).lower ∧
    (cell12899 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12899 i).upper ≤ (0.532 : ℝ) ∧
    (cell12899 i).centre ≤ (0.1 : ℝ) ∧ (cell12899 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12899 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12899 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12899

/-! The local source numeric instances at 12899 have no network premises. -/
namespace BstLean.Part269.N12899
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12899)
open BstLean.Part268 (cell12899)

noncomputable def sourceNumerics12899 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12899 (cell12899 i)
      scalarRow12899.M scalarRow12899.H scalarRow12899.xi := by
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
    energy_allowance := scalarRow12899.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12899]
    centre_nonneg := (scalarRow12899.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12899])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12899