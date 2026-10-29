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
/-! Actual 12875 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12875
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12875 ≤ (1.035562891551 : ℝ) := by
  have hr : (113.468057179102 : ℝ) ≤ √(12875 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.468057179102 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12875 12875 (11 / 1000) ≤
    (0.008424282595 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12875) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.468057179102 : ℝ) ≤ √(12875 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12875)
  have hdiv : K / √(12875 : ℝ) ≤ K / 113.468057179102 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.468057179102 ≤ (0.008424282595 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12875.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12875 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12875 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12875 := gPlus_lower 12875
end BstLean.Part269.N12875

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12875
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035562891550 : ℝ) ≤ wn 12875 := by
  have hn : √(12875 : ℝ) ≤ 113.468057179103 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12875 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.468057179103 ≤ 2 / √(12875 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248398159 : ℝ) ≤ rhoBar 12875 BstLean.Part154.csC ∧
    rhoBar 12875 BstLean.Part154.csC ≤ 0.000248398544 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035562891550 : ℝ) / (1.295212 * 12875) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035562891551 : ℝ) / (1.29521 * 12875) := by gcongr
      _ ≤ (0.000248398544 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12875 BstLean.Part154.csC) ≤ 0.000993655878 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12875 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12875 BstLean.Part154.csC) (piBar (rhoBar 12875 BstLean.Part154.csC)) ≤ 0.000189728362 ∧
    cc1 (rhoBar 12875 BstLean.Part154.csC) (piBar (rhoBar 12875 BstLean.Part154.csC)) ≤ 0.000120725441 ∧
    cc2 (rhoBar 12875 BstLean.Part154.csC) ≤ 0.000070082074 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12875 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12875 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12875 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12875 BstLean.Part154.csC * nuR (rhoBar 12875 BstLean.Part154.csC)) ≤ 0.000496812514 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248398544 : ℝ) * 0.000993655878 := by gcongr
      _ ≤ (0.000496812514 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12875 BstLean.Part154.csC) * nuR (rhoBar 12875 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000993655878 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12875 BstLean.Part154.csC) * rhoBar 12875 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248398544 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248398544 / 2 + 0.399 * 0.000993655878 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189728362 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496812514 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120725441 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248398544 / 1.414213562 := by gcongr
      _ ≤ (0.000070082074 : ℝ) := by norm_num

end BstLean.Part269.N12875

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12875
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12875 BstLean.Part154.csC) (piBar (rhoBar 12875 BstLean.Part154.csC)) ≤ 1.55453E-7 := by
  have hr0 : 0 ≤ rhoBar 12875 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12875 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12875 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12875 BstLean.Part154.csC) (piBar (rhoBar 12875 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12875 BstLean.Part154.csC) (piBar (rhoBar 12875 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12875 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189728362 : ℝ) ^ 2 + 0.000120725441 ^ 2 + 3 * 0.000070082074 ^ 2 +
        2 * 0.797885 * 0.000189728362 * 0.000120725441 + 2 * 0.000189728362 * 0.000070082074 +
        4 * 0.797885 * 0.000120725441 * 0.000070082074 := by gcongr
    _ ≤ (1.55453E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12875 BstLean.Part154.csC Θ ≤ 0.002592311616 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12875 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12875 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12875 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12875 BstLean.Part154.csC) (piBar (rhoBar 12875 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12875 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035562891551 * 1.55453E-7 / (0.000248398159 : ℝ) := by gcongr
    _ ≤ 0.002592311616 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12875 BstLean.Part154.csC Θ ≤ 0.002875629810 + 0.000655036847 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12875 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12875 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12875 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035562891551 : ℝ) * ((2 * Θ * 0.000248398544 +
        (6863 / 10000) * 0.000248398544 * 12875 * 0.000993655878) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002875629810 + 0.000655036847 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12875 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12875 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12875 0.011 Θ ∧ gammaRatio 12875 0.011 Θ ≤ 0.000085392996 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12875 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035562891551 : ℝ) * 0.525 / ((1 - 0.011) * 12875) := by gcongr
      _ ≤ (0.000085392996 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12875 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12875 0.011 Θ) :=
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
    badAllowance 12875 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12875 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12875 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12875 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12875 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12875 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12875 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12875 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12875 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12875 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12875 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035562891551 : ℝ) * 12875 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12875 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003338665865 + 0.003247348463 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12875

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12875
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12875 BstLean.Part154.csC) (piBar (rhoBar 12875 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12875 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12875 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12875 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12875 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12875 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12875 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12875 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12875 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12875 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12875 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12875 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12875 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12875 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12875 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052122548417 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12875) ≤ 0.010524879079 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12875 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035562891551)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010524879079 + 2 * 0.737676 / 12875) := by gcongr
    _ ≤ (0.052122548417 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12875 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12875

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12875
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511374741 : ℝ) ≤ plow 12875 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12875) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052550123809)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360963599) : eMP 12875 0.011 xi bn ≤ 0.001171893204 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12875 : ℝ) * (1 - 0.011))) ≤ 0.000579463988 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001360963599 / (12875 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579463988 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579463988 : ℝ) + 3.141593 * 0.052550123809 / (12875 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001171893204 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052550123809)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360963599) : PiBarMP 12875 12 0.011 xi bn ≤ 0.160140196553 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12875 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036891240140 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.842257155730 : ℝ) ≤ √((12875 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.468057179102 : ℝ) ≤ √(12875 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12875) ≤ 0.122787052226 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036891240140 + 0.052550123809 * 1.772454 / (2 * (112.842257155730 : ℝ))) * (1 + 0.001171893204) +
        8 / (12875 * 113.468057179102) + 0.122787052226 := by gcongr
    _ ≤ (0.160140196553 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052550123809)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360963599) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281360686189) :
    parallelOracle 12875 0.011 xi bn cd ≤ 0.161116774575 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12875 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12875 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511374741 : ℝ) ≤ plow 12875 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.468057179102 : ℝ) ≤ √(12875 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281360686189 : ℝ) / (2 * 0.560511374741 * 113.468057179102)) * 0.160140196553 +
        0.281360686189 ^ 2 / (2 * 0.560511374741 * 113.468057179102) := by gcongr
    _ ≤ (0.161116774575 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052550123809) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360963599)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281360686189) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12875 12875 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511374741 : ℝ) ≤ plow 12875 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.468057179102 : ℝ) ≤ √(12875 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12875 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12875 Θ 1.22 ≤ 0.011686993970 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.468057179102 := by gcongr <;> linarith
      _ ≤ (0.011686993970 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12875 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12875 12875 0.011 ≤ 0.008424282595 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12875 12875 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12875 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12875 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12875 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12875 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161116774575 + 0.011686993970 + (0.008424282595 : ℝ) *
        (1 + 2 * (0.281360686189 + 0.011686993970) / (0.560511374741 * 113.468057179102))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12875]

end BstLean.Part269.N12875

/-! The original eight local profiles supply actual 12875 moment certificates. -/
namespace BstLean.Part269.N12875
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12875 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12875 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12875 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052550123809 ∧
    0 ≤ bN 12875 BstLean.Part154.csC (groupTheta g) ∧ bN 12875 BstLean.Part154.csC (groupTheta g) ≤ 0.001360963599 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12875 12875 0.011
      (momentAllowance 12875 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12875 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12875 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12875 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12875 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12875 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229238137772 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12875 0.011
      (momentAllowance 12875 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12875 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12875
/-! The actual computed-centre upper energy formula at 12875. -/
namespace BstLean.Part269.N12875
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12875

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12875
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12875)
open BstLean.Part268 (cell12875)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084995574708
  | 2 => 0.085929580342
  | 3 => 0.086860506543
  | 4 => 0.087789486748
  | 5 => 0.088717900659
  | 6 => 0.089647411934
  | 7 => 0.090580009620
  | 8 => 0.091518053433
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12875 12875 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12875 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12875

/-! Actual upper energy certificates on all 43 source endpoints at 12875. -/
namespace BstLean.Part269.N12875
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12875)
open BstLean.Part268 (cell12875)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12875 (gMinus 12875) (1 - (cell12875 i).lower) ≤ 1 ∧
    energyUpper 12875 (gMinus 12875) (BstLean.Part211.gPlus 12875)
      (finiteEnergy 12875 12875 0.011) (1 - (cell12875 i).lower) ≤
      (cell12875 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨10,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨11,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨12,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨13,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨14,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨15,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨16,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨17,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨18,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨19,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨20,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨21,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨22,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨23,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨24,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨25,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨26,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨27,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨28,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨29,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨30,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨31,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨32,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨33,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨34,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨35,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨36,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨37,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨38,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨39,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨40,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨41,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨42,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨43,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨44,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨45,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨46,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨47,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨48,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨49,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨50,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨51,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12875) (by norm_num)
        (q := 1 - (cell12875 ⟨52,by decide⟩).lower)
        (by norm_num [cell12875]) (by norm_num [cell12875])
      exact ⟨E.1,E.2.trans (by norm_num [cell12875])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12875

/-! Source-cell containment and simple scalar guards at 12875. -/
namespace BstLean.Part269.N12875
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12875)
open BstLean.Part268 (cell12875)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12875 ⟨10,by decide⟩).lower ∧ (cell12875 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12875 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12875 ⟨11,by decide⟩).lower ∧ (cell12875 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12875 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12875 ⟨12,by decide⟩).lower ∧ (cell12875 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12875 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12875 ⟨13,by decide⟩).lower ∧ (cell12875 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12875 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12875 ⟨14,by decide⟩).lower ∧ (cell12875 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12875 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12875 ⟨15,by decide⟩).lower ∧ (cell12875 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12875 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12875 ⟨16,by decide⟩).lower ∧ (cell12875 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12875 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12875 ⟨17,by decide⟩).lower ∧ (cell12875 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12875 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12875 ⟨18,by decide⟩).lower ∧ (cell12875 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12875 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12875 ⟨19,by decide⟩).lower ∧ (cell12875 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12875 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12875 ⟨20,by decide⟩).lower ∧ (cell12875 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12875 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12875 ⟨21,by decide⟩).lower ∧ (cell12875 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12875 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12875 ⟨22,by decide⟩).lower ∧ (cell12875 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12875 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12875 ⟨23,by decide⟩).lower ∧ (cell12875 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12875 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12875 ⟨24,by decide⟩).lower ∧ (cell12875 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12875 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12875 ⟨25,by decide⟩).lower ∧ (cell12875 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12875 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12875 ⟨26,by decide⟩).lower ∧ (cell12875 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12875 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12875 ⟨27,by decide⟩).lower ∧ (cell12875 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12875 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12875 ⟨28,by decide⟩).lower ∧ (cell12875 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12875 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12875 ⟨29,by decide⟩).lower ∧ (cell12875 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12875 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12875 ⟨30,by decide⟩).lower ∧ (cell12875 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12875 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12875 ⟨31,by decide⟩).lower ∧ (cell12875 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12875 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12875 ⟨32,by decide⟩).lower ∧ (cell12875 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12875 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12875 ⟨33,by decide⟩).lower ∧ (cell12875 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12875 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12875 ⟨34,by decide⟩).lower ∧ (cell12875 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12875 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12875 ⟨35,by decide⟩).lower ∧ (cell12875 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12875 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12875 ⟨36,by decide⟩).lower ∧ (cell12875 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12875 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12875 ⟨37,by decide⟩).lower ∧ (cell12875 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12875 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12875 ⟨38,by decide⟩).lower ∧ (cell12875 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12875 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12875 ⟨39,by decide⟩).lower ∧ (cell12875 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12875 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12875 ⟨40,by decide⟩).lower ∧ (cell12875 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12875 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12875 ⟨41,by decide⟩).lower ∧ (cell12875 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12875 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12875 ⟨42,by decide⟩).lower ∧ (cell12875 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12875 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12875 ⟨43,by decide⟩).lower ∧ (cell12875 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12875 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12875 ⟨44,by decide⟩).lower ∧ (cell12875 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12875 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12875 ⟨45,by decide⟩).lower ∧ (cell12875 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12875 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12875 ⟨46,by decide⟩).lower ∧ (cell12875 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12875 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12875 ⟨47,by decide⟩).lower ∧ (cell12875 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12875 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12875 ⟨48,by decide⟩).lower ∧ (cell12875 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12875 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12875 ⟨49,by decide⟩).lower ∧ (cell12875 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12875 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12875 ⟨50,by decide⟩).lower ∧ (cell12875 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12875 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12875 ⟨51,by decide⟩).lower ∧ (cell12875 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12875 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12875 ⟨52,by decide⟩).lower ∧ (cell12875 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12875 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12875 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12875 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12875,cell12875,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12875 i).lower ∧
    (cell12875 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12875 i).upper ≤ (0.532 : ℝ) ∧
    (cell12875 i).centre ≤ (0.1 : ℝ) ∧ (cell12875 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12875 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12875 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12875

/-! The local source numeric instances at 12875 have no network premises. -/
namespace BstLean.Part269.N12875
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12875)
open BstLean.Part268 (cell12875)

noncomputable def sourceNumerics12875 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12875 (cell12875 i)
      scalarRow12875.M scalarRow12875.H scalarRow12875.xi := by
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
    energy_allowance := scalarRow12875.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12875]
    centre_nonneg := (scalarRow12875.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12875])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12875
/-! Actual 12876 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12876
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12876 ≤ (1.035561498485 : ℝ) := by
  have hr : (113.472463620034 : ℝ) ≤ √(12876 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.472463620034 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12876 12876 (11 / 1000) ≤
    (0.008423955455 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12876) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.472463620034 : ℝ) ≤ √(12876 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12876)
  have hdiv : K / √(12876 : ℝ) ≤ K / 113.472463620034 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.472463620034 ≤ (0.008423955455 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12876.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12876 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12876 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12876 := gPlus_lower 12876
end BstLean.Part269.N12876

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12876
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035561498484 : ℝ) ≤ wn 12876 := by
  have hn : √(12876 : ℝ) ≤ 113.472463620035 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12876 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.472463620035 ≤ 2 / √(12876 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248378533 : ℝ) ≤ rhoBar 12876 BstLean.Part154.csC ∧
    rhoBar 12876 BstLean.Part154.csC ≤ 0.000248378918 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035561498484 : ℝ) / (1.295212 * 12876) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035561498485 : ℝ) / (1.29521 * 12876) := by gcongr
      _ ≤ (0.000248378918 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12876 BstLean.Part154.csC) ≤ 0.000993577365 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12876 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12876 BstLean.Part154.csC) (piBar (rhoBar 12876 BstLean.Part154.csC)) ≤ 0.000189713371 ∧
    cc1 (rhoBar 12876 BstLean.Part154.csC) (piBar (rhoBar 12876 BstLean.Part154.csC)) ≤ 0.000120715903 ∧
    cc2 (rhoBar 12876 BstLean.Part154.csC) ≤ 0.000070076537 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12876 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12876 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12876 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12876 BstLean.Part154.csC * nuR (rhoBar 12876 BstLean.Part154.csC)) ≤ 0.000496773260 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248378918 : ℝ) * 0.000993577365 := by gcongr
      _ ≤ (0.000496773260 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12876 BstLean.Part154.csC) * nuR (rhoBar 12876 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000993577365 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12876 BstLean.Part154.csC) * rhoBar 12876 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248378918 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248378918 / 2 + 0.399 * 0.000993577365 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189713371 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496773260 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120715903 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248378918 / 1.414213562 := by gcongr
      _ ≤ (0.000070076537 : ℝ) := by norm_num

end BstLean.Part269.N12876

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12876
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12876 BstLean.Part154.csC) (piBar (rhoBar 12876 BstLean.Part154.csC)) ≤ 1.55429E-7 := by
  have hr0 : 0 ≤ rhoBar 12876 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12876 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12876 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12876 BstLean.Part154.csC) (piBar (rhoBar 12876 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12876 BstLean.Part154.csC) (piBar (rhoBar 12876 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12876 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189713371 : ℝ) ^ 2 + 0.000120715903 ^ 2 + 3 * 0.000070076537 ^ 2 +
        2 * 0.797885 * 0.000189713371 * 0.000120715903 + 2 * 0.000189713371 * 0.000070076537 +
        4 * 0.797885 * 0.000120715903 * 0.000070076537 := by gcongr
    _ ≤ (1.55429E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12876 BstLean.Part154.csC Θ ≤ 0.002592112712 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12876 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12876 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12876 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12876 BstLean.Part154.csC) (piBar (rhoBar 12876 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12876 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035561498485 * 1.55429E-7 / (0.000248378533 : ℝ) := by gcongr
    _ ≤ 0.002592112712 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12876 BstLean.Part154.csC Θ ≤ 0.002875394855 + 0.000654984211 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12876 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12876 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12876 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035561498485 : ℝ) * ((2 * Θ * 0.000248378918 +
        (6863 / 10000) * 0.000248378918 * 12876 * 0.000993577365) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002875394855 + 0.000654984211 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12876 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12876 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12876 0.011 Θ ∧ gammaRatio 12876 0.011 Θ ≤ 0.000085386249 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12876 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035561498485 : ℝ) * 0.525 / ((1 - 0.011) * 12876) := by gcongr
      _ ≤ (0.000085386249 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12876 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12876 0.011 Θ) :=
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
    badAllowance 12876 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12876 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12876 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12876 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12876 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12876 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12876 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12876 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12876 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12876 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12876 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035561498485 : ℝ) * 12876 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12876 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003338430910 + 0.003247096923 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12876

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12876
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12876 BstLean.Part154.csC) (piBar (rhoBar 12876 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12876 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12876 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12876 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12876 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12876 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12876 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12876 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12876 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12876 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12876 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12876 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12876 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12876 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12876 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052120502556 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12876) ≤ 0.010524470369 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12876 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035561498485)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010524470369 + 2 * 0.737676 / 12876) := by gcongr
    _ ≤ (0.052120502556 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12876 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12876

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12876
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511418740 : ℝ) ≤ plow 12876 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12876) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052549756795)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360859174) : eMP 12876 0.011 xi bn ≤ 0.001171802640 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12876 : ℝ) * (1 - 0.011))) ≤ 0.000579419255 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001360859174 / (12876 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579419255 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579419255 : ℝ) + 3.141593 * 0.052549756795 / (12876 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001171802640 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052549756795)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360859174) : PiBarMP 12876 12 0.011 xi bn ≤ 0.160133988459 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12876 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036889824804 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.846639294220 : ℝ) ≤ √((12876 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.472463620034 : ℝ) ≤ √(12876 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12876) ≤ 0.122782284074 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036889824804 + 0.052549756795 * 1.772454 / (2 * (112.846639294220 : ℝ))) * (1 + 0.001171802640) +
        8 / (12876 * 113.472463620034) + 0.122782284074 := by gcongr
    _ ≤ (0.160133988459 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052549756795)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360859174) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281357839819) :
    parallelOracle 12876 0.011 xi bn cd ≤ 0.161110498575 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12876 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12876 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511418740 : ℝ) ≤ plow 12876 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.472463620034 : ℝ) ≤ √(12876 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281357839819 : ℝ) / (2 * 0.560511418740 * 113.472463620034)) * 0.160133988459 +
        0.281357839819 ^ 2 / (2 * 0.560511418740 * 113.472463620034) := by gcongr
    _ ≤ (0.161110498575 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052549756795) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360859174)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281357839819) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12876 12876 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511418740 : ℝ) ≤ plow 12876 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.472463620034 : ℝ) ≤ √(12876 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12876 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12876 Θ 1.22 ≤ 0.011686540133 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.472463620034 := by gcongr <;> linarith
      _ ≤ (0.011686540133 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12876 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12876 12876 0.011 ≤ 0.008423955455 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12876 12876 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12876 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12876 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12876 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12876 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161110498575 + 0.011686540133 + (0.008423955455 : ℝ) *
        (1 + 2 * (0.281357839819 + 0.011686540133) / (0.560511418740 * 113.472463620034))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12876]

end BstLean.Part269.N12876

/-! The original eight local profiles supply actual 12876 moment certificates. -/
namespace BstLean.Part269.N12876
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12876 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12876 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12876 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052549756795 ∧
    0 ≤ bN 12876 BstLean.Part154.csC (groupTheta g) ∧ bN 12876 BstLean.Part154.csC (groupTheta g) ≤ 0.001360859174 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12876 12876 0.011
      (momentAllowance 12876 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12876 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12876 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12876 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12876 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12876 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229237337263 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12876 0.011
      (momentAllowance 12876 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12876 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12876
/-! The actual computed-centre upper energy formula at 12876. -/
namespace BstLean.Part269.N12876
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12876

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12876
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12876)
open BstLean.Part268 (cell12876)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084992832942
  | 2 => 0.085926791983
  | 3 => 0.086857665418
  | 4 => 0.087786585221
  | 5 => 0.088714929367
  | 6 => 0.089644359485
  | 7 => 0.090576862261
  | 8 => 0.091514794671
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12876 12876 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12876 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12876

/-! Actual upper energy certificates on all 43 source endpoints at 12876. -/
namespace BstLean.Part269.N12876
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12876)
open BstLean.Part268 (cell12876)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12876 (gMinus 12876) (1 - (cell12876 i).lower) ≤ 1 ∧
    energyUpper 12876 (gMinus 12876) (BstLean.Part211.gPlus 12876)
      (finiteEnergy 12876 12876 0.011) (1 - (cell12876 i).lower) ≤
      (cell12876 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨10,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨11,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨12,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨13,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨14,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨15,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨16,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨17,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨18,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨19,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨20,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨21,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨22,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨23,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨24,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨25,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨26,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨27,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨28,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨29,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨30,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨31,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨32,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨33,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨34,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨35,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨36,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨37,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨38,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨39,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨40,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨41,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨42,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨43,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨44,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨45,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨46,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨47,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨48,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨49,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨50,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨51,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12876) (by norm_num)
        (q := 1 - (cell12876 ⟨52,by decide⟩).lower)
        (by norm_num [cell12876]) (by norm_num [cell12876])
      exact ⟨E.1,E.2.trans (by norm_num [cell12876])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12876

/-! Source-cell containment and simple scalar guards at 12876. -/
namespace BstLean.Part269.N12876
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12876)
open BstLean.Part268 (cell12876)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12876 ⟨10,by decide⟩).lower ∧ (cell12876 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12876 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12876 ⟨11,by decide⟩).lower ∧ (cell12876 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12876 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12876 ⟨12,by decide⟩).lower ∧ (cell12876 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12876 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12876 ⟨13,by decide⟩).lower ∧ (cell12876 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12876 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12876 ⟨14,by decide⟩).lower ∧ (cell12876 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12876 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12876 ⟨15,by decide⟩).lower ∧ (cell12876 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12876 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12876 ⟨16,by decide⟩).lower ∧ (cell12876 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12876 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12876 ⟨17,by decide⟩).lower ∧ (cell12876 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12876 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12876 ⟨18,by decide⟩).lower ∧ (cell12876 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12876 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12876 ⟨19,by decide⟩).lower ∧ (cell12876 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12876 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12876 ⟨20,by decide⟩).lower ∧ (cell12876 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12876 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12876 ⟨21,by decide⟩).lower ∧ (cell12876 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12876 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12876 ⟨22,by decide⟩).lower ∧ (cell12876 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12876 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12876 ⟨23,by decide⟩).lower ∧ (cell12876 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12876 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12876 ⟨24,by decide⟩).lower ∧ (cell12876 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12876 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12876 ⟨25,by decide⟩).lower ∧ (cell12876 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12876 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12876 ⟨26,by decide⟩).lower ∧ (cell12876 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12876 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12876 ⟨27,by decide⟩).lower ∧ (cell12876 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12876 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12876 ⟨28,by decide⟩).lower ∧ (cell12876 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12876 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12876 ⟨29,by decide⟩).lower ∧ (cell12876 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12876 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12876 ⟨30,by decide⟩).lower ∧ (cell12876 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12876 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12876 ⟨31,by decide⟩).lower ∧ (cell12876 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12876 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12876 ⟨32,by decide⟩).lower ∧ (cell12876 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12876 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12876 ⟨33,by decide⟩).lower ∧ (cell12876 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12876 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12876 ⟨34,by decide⟩).lower ∧ (cell12876 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12876 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12876 ⟨35,by decide⟩).lower ∧ (cell12876 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12876 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12876 ⟨36,by decide⟩).lower ∧ (cell12876 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12876 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12876 ⟨37,by decide⟩).lower ∧ (cell12876 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12876 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12876 ⟨38,by decide⟩).lower ∧ (cell12876 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12876 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12876 ⟨39,by decide⟩).lower ∧ (cell12876 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12876 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12876 ⟨40,by decide⟩).lower ∧ (cell12876 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12876 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12876 ⟨41,by decide⟩).lower ∧ (cell12876 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12876 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12876 ⟨42,by decide⟩).lower ∧ (cell12876 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12876 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12876 ⟨43,by decide⟩).lower ∧ (cell12876 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12876 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12876 ⟨44,by decide⟩).lower ∧ (cell12876 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12876 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12876 ⟨45,by decide⟩).lower ∧ (cell12876 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12876 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12876 ⟨46,by decide⟩).lower ∧ (cell12876 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12876 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12876 ⟨47,by decide⟩).lower ∧ (cell12876 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12876 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12876 ⟨48,by decide⟩).lower ∧ (cell12876 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12876 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12876 ⟨49,by decide⟩).lower ∧ (cell12876 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12876 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12876 ⟨50,by decide⟩).lower ∧ (cell12876 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12876 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12876 ⟨51,by decide⟩).lower ∧ (cell12876 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12876 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12876 ⟨52,by decide⟩).lower ∧ (cell12876 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12876 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12876 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12876 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12876,cell12876,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12876 i).lower ∧
    (cell12876 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12876 i).upper ≤ (0.532 : ℝ) ∧
    (cell12876 i).centre ≤ (0.1 : ℝ) ∧ (cell12876 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12876 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12876 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12876

/-! The local source numeric instances at 12876 have no network premises. -/
namespace BstLean.Part269.N12876
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12876)
open BstLean.Part268 (cell12876)

noncomputable def sourceNumerics12876 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12876 (cell12876 i)
      scalarRow12876.M scalarRow12876.H scalarRow12876.xi := by
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
    energy_allowance := scalarRow12876.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12876]
    centre_nonneg := (scalarRow12876.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12876])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12876
/-! Actual 12877 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12877
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12877 ≤ (1.035560105581 : ℝ) := by
  have hr : (113.476869889859 : ℝ) ≤ √(12877 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.476869889859 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12877 12877 (11 / 1000) ≤
    (0.008423628353 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12877) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.476869889859 : ℝ) ≤ √(12877 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12877)
  have hdiv : K / √(12877 : ℝ) ≤ K / 113.476869889859 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.476869889859 ≤ (0.008423628353 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12877.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12877 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12877 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12877 := gPlus_lower 12877
end BstLean.Part269.N12877

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12877
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035560105580 : ℝ) ≤ wn 12877 := by
  have hn : √(12877 : ℝ) ≤ 113.476869889860 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12877 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.476869889860 ≤ 2 / √(12877 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248358911 : ℝ) ≤ rhoBar 12877 BstLean.Part154.csC ∧
    rhoBar 12877 BstLean.Part154.csC ≤ 0.000248359295 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035560105580 : ℝ) / (1.295212 * 12877) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035560105581 : ℝ) / (1.29521 * 12877) := by gcongr
      _ ≤ (0.000248359295 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12877 BstLean.Part154.csC) ≤ 0.000993498863 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12877 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12877 BstLean.Part154.csC) (piBar (rhoBar 12877 BstLean.Part154.csC)) ≤ 0.000189698382 ∧
    cc1 (rhoBar 12877 BstLean.Part154.csC) (piBar (rhoBar 12877 BstLean.Part154.csC)) ≤ 0.000120706365 ∧
    cc2 (rhoBar 12877 BstLean.Part154.csC) ≤ 0.000070071001 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12877 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12877 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12877 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12877 BstLean.Part154.csC * nuR (rhoBar 12877 BstLean.Part154.csC)) ≤ 0.000496734011 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248359295 : ℝ) * 0.000993498863 := by gcongr
      _ ≤ (0.000496734011 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12877 BstLean.Part154.csC) * nuR (rhoBar 12877 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000993498863 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12877 BstLean.Part154.csC) * rhoBar 12877 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248359295 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248359295 / 2 + 0.399 * 0.000993498863 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189698382 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496734011 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120706365 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248359295 / 1.414213562 := by gcongr
      _ ≤ (0.000070071001 : ℝ) := by norm_num

end BstLean.Part269.N12877

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12877
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12877 BstLean.Part154.csC) (piBar (rhoBar 12877 BstLean.Part154.csC)) ≤ 1.55404E-7 := by
  have hr0 : 0 ≤ rhoBar 12877 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12877 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12877 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12877 BstLean.Part154.csC) (piBar (rhoBar 12877 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12877 BstLean.Part154.csC) (piBar (rhoBar 12877 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12877 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189698382 : ℝ) ^ 2 + 0.000120706365 ^ 2 + 3 * 0.000070071001 ^ 2 +
        2 * 0.797885 * 0.000189698382 * 0.000120706365 + 2 * 0.000189698382 * 0.000070071001 +
        4 * 0.797885 * 0.000120706365 * 0.000070071001 := by gcongr
    _ ≤ (1.55404E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12877 BstLean.Part154.csC Θ ≤ 0.002591897058 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12877 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12877 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12877 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12877 BstLean.Part154.csC) (piBar (rhoBar 12877 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12877 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035560105581 * 1.55404E-7 / (0.000248358911 : ℝ) := by gcongr
    _ ≤ 0.002591897058 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12877 BstLean.Part154.csC Θ ≤ 0.002875159932 + 0.000654931584 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12877 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12877 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12877 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035560105581 : ℝ) * ((2 * Θ * 0.000248359295 +
        (6863 / 10000) * 0.000248359295 * 12877 * 0.000993498863) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002875159932 + 0.000654931584 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12877 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12877 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12877 0.011 Θ ∧ gammaRatio 12877 0.011 Θ ≤ 0.000085379504 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12877 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035560105581 : ℝ) * 0.525 / ((1 - 0.011) * 12877) := by gcongr
      _ ≤ (0.000085379504 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12877 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12877 0.011 Θ) :=
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
    badAllowance 12877 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12877 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12877 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12877 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12877 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12877 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12877 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12877 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12877 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12877 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12877 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035560105581 : ℝ) * 12877 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12877 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003338195987 + 0.003246828642 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12877

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12877
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12877 BstLean.Part154.csC) (piBar (rhoBar 12877 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12877 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12877 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12877 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12877 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12877 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12877 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12877 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12877 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12877 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12877 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12877 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12877 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12877 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12877 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052118456942 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12877) ≤ 0.010524061708 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12877 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035560105581)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010524061708 + 2 * 0.737676 / 12877) := by gcongr
    _ ≤ (0.052118456942 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12877 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12877

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12877
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511462732 : ℝ) ≤ plow 12877 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12877) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052549381025)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360745956) : eMP 12877 0.011 xi bn ≤ 0.001171708339 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12877 : ℝ) * (1 - 0.011))) ≤ 0.000579372654 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001360745956 / (12877 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579372654 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579372654 : ℝ) + 3.141593 * 0.052549381025 / (12877 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001171708339 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052549381025)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360745956) : PiBarMP 12877 12 0.011 xi bn ≤ 0.160127661336 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12877 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036888290229 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.851021262547 : ℝ) ≤ √((12877 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.476869889859 : ℝ) ≤ √(12877 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12877) ≤ 0.122777516478 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036888290229 + 0.052549381025 * 1.772454 / (2 * (112.851021262547 : ℝ))) * (1 + 0.001171708339) +
        8 / (12877 * 113.476869889859) + 0.122777516478 := by gcongr
    _ ≤ (0.160127661336 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052549381025)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360745956) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281354974594) :
    parallelOracle 12877 0.011 xi bn cd ≤ 0.161104103182 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12877 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12877 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511462732 : ℝ) ≤ plow 12877 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.476869889859 : ℝ) ≤ √(12877 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281354974594 : ℝ) / (2 * 0.560511462732 * 113.476869889859)) * 0.160127661336 +
        0.281354974594 ^ 2 / (2 * 0.560511462732 * 113.476869889859) := by gcongr
    _ ≤ (0.161104103182 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052549381025) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360745956)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281354974594) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12877 12877 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511462732 : ℝ) ≤ plow 12877 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.476869889859 : ℝ) ≤ √(12877 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12877 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12877 Θ 1.22 ≤ 0.011686086348 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.476869889859 := by gcongr <;> linarith
      _ ≤ (0.011686086348 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12877 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12877 12877 0.011 ≤ 0.008423628353 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12877 12877 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12877 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12877 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12877 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12877 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161104103182 + 0.011686086348 + (0.008423628353 : ℝ) *
        (1 + 2 * (0.281354974594 + 0.011686086348) / (0.560511462732 * 113.476869889859))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12877]

end BstLean.Part269.N12877

/-! The original eight local profiles supply actual 12877 moment certificates. -/
namespace BstLean.Part269.N12877
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12877 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12877 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12877 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052549381025 ∧
    0 ≤ bN 12877 BstLean.Part154.csC (groupTheta g) ∧ bN 12877 BstLean.Part154.csC (groupTheta g) ≤ 0.001360745956 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12877 12877 0.011
      (momentAllowance 12877 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12877 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12877 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12877 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12877 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12877 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229236517652 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12877 0.011
      (momentAllowance 12877 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12877 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12877
/-! The actual computed-centre upper energy formula at 12877. -/
namespace BstLean.Part269.N12877
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12877

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12877
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12877)
open BstLean.Part268 (cell12877)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084990092087
  | 2 => 0.085924004570
  | 3 => 0.086854825283
  | 4 => 0.087783684738
  | 5 => 0.088711959185
  | 6 => 0.089641308227
  | 7 => 0.090573716189
  | 8 => 0.091511537314
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12877 12877 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12877 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12877

/-! Actual upper energy certificates on all 43 source endpoints at 12877. -/
namespace BstLean.Part269.N12877
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12877)
open BstLean.Part268 (cell12877)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12877 (gMinus 12877) (1 - (cell12877 i).lower) ≤ 1 ∧
    energyUpper 12877 (gMinus 12877) (BstLean.Part211.gPlus 12877)
      (finiteEnergy 12877 12877 0.011) (1 - (cell12877 i).lower) ≤
      (cell12877 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨10,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨11,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨12,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨13,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨14,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨15,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨16,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨17,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨18,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨19,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨20,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨21,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨22,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨23,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨24,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨25,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨26,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨27,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨28,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨29,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨30,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨31,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨32,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨33,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨34,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨35,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨36,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨37,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨38,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨39,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨40,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨41,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨42,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨43,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨44,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨45,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨46,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨47,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨48,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨49,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨50,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨51,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12877) (by norm_num)
        (q := 1 - (cell12877 ⟨52,by decide⟩).lower)
        (by norm_num [cell12877]) (by norm_num [cell12877])
      exact ⟨E.1,E.2.trans (by norm_num [cell12877])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12877

/-! Source-cell containment and simple scalar guards at 12877. -/
namespace BstLean.Part269.N12877
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12877)
open BstLean.Part268 (cell12877)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12877 ⟨10,by decide⟩).lower ∧ (cell12877 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12877 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12877 ⟨11,by decide⟩).lower ∧ (cell12877 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12877 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12877 ⟨12,by decide⟩).lower ∧ (cell12877 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12877 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12877 ⟨13,by decide⟩).lower ∧ (cell12877 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12877 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12877 ⟨14,by decide⟩).lower ∧ (cell12877 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12877 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12877 ⟨15,by decide⟩).lower ∧ (cell12877 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12877 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12877 ⟨16,by decide⟩).lower ∧ (cell12877 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12877 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12877 ⟨17,by decide⟩).lower ∧ (cell12877 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12877 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12877 ⟨18,by decide⟩).lower ∧ (cell12877 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12877 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12877 ⟨19,by decide⟩).lower ∧ (cell12877 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12877 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12877 ⟨20,by decide⟩).lower ∧ (cell12877 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12877 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12877 ⟨21,by decide⟩).lower ∧ (cell12877 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12877 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12877 ⟨22,by decide⟩).lower ∧ (cell12877 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12877 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12877 ⟨23,by decide⟩).lower ∧ (cell12877 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12877 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12877 ⟨24,by decide⟩).lower ∧ (cell12877 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12877 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12877 ⟨25,by decide⟩).lower ∧ (cell12877 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12877 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12877 ⟨26,by decide⟩).lower ∧ (cell12877 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12877 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12877 ⟨27,by decide⟩).lower ∧ (cell12877 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12877 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12877 ⟨28,by decide⟩).lower ∧ (cell12877 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12877 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12877 ⟨29,by decide⟩).lower ∧ (cell12877 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12877 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12877 ⟨30,by decide⟩).lower ∧ (cell12877 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12877 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12877 ⟨31,by decide⟩).lower ∧ (cell12877 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12877 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12877 ⟨32,by decide⟩).lower ∧ (cell12877 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12877 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12877 ⟨33,by decide⟩).lower ∧ (cell12877 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12877 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12877 ⟨34,by decide⟩).lower ∧ (cell12877 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12877 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12877 ⟨35,by decide⟩).lower ∧ (cell12877 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12877 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12877 ⟨36,by decide⟩).lower ∧ (cell12877 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12877 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12877 ⟨37,by decide⟩).lower ∧ (cell12877 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12877 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12877 ⟨38,by decide⟩).lower ∧ (cell12877 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12877 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12877 ⟨39,by decide⟩).lower ∧ (cell12877 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12877 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12877 ⟨40,by decide⟩).lower ∧ (cell12877 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12877 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12877 ⟨41,by decide⟩).lower ∧ (cell12877 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12877 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12877 ⟨42,by decide⟩).lower ∧ (cell12877 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12877 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12877 ⟨43,by decide⟩).lower ∧ (cell12877 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12877 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12877 ⟨44,by decide⟩).lower ∧ (cell12877 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12877 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12877 ⟨45,by decide⟩).lower ∧ (cell12877 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12877 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12877 ⟨46,by decide⟩).lower ∧ (cell12877 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12877 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12877 ⟨47,by decide⟩).lower ∧ (cell12877 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12877 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12877 ⟨48,by decide⟩).lower ∧ (cell12877 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12877 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12877 ⟨49,by decide⟩).lower ∧ (cell12877 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12877 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12877 ⟨50,by decide⟩).lower ∧ (cell12877 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12877 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12877 ⟨51,by decide⟩).lower ∧ (cell12877 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12877 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12877 ⟨52,by decide⟩).lower ∧ (cell12877 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12877 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12877 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12877 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12877,cell12877,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12877 i).lower ∧
    (cell12877 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12877 i).upper ≤ (0.532 : ℝ) ∧
    (cell12877 i).centre ≤ (0.1 : ℝ) ∧ (cell12877 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12877 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12877 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12877

/-! The local source numeric instances at 12877 have no network premises. -/
namespace BstLean.Part269.N12877
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12877)
open BstLean.Part268 (cell12877)

noncomputable def sourceNumerics12877 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12877 (cell12877 i)
      scalarRow12877.M scalarRow12877.H scalarRow12877.xi := by
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
    energy_allowance := scalarRow12877.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12877]
    centre_nonneg := (scalarRow12877.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12877])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12877
/-! Actual 12878 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12878
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12878 ≤ (1.035558712841 : ℝ) := by
  have hr : (113.481275988596 : ℝ) ≤ √(12878 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.481275988596 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12878 12878 (11 / 1000) ≤
    (0.008423301289 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12878) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.481275988596 : ℝ) ≤ √(12878 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12878)
  have hdiv : K / √(12878 : ℝ) ≤ K / 113.481275988596 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.481275988596 ≤ (0.008423301289 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12878.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12878 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12878 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12878 := gPlus_lower 12878
end BstLean.Part269.N12878

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12878
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035558712840 : ℝ) ≤ wn 12878 := by
  have hn : √(12878 : ℝ) ≤ 113.481275988597 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12878 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.481275988597 ≤ 2 / √(12878 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248339291 : ℝ) ≤ rhoBar 12878 BstLean.Part154.csC ∧
    rhoBar 12878 BstLean.Part154.csC ≤ 0.000248339676 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035558712840 : ℝ) / (1.295212 * 12878) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035558712841 : ℝ) / (1.29521 * 12878) := by gcongr
      _ ≤ (0.000248339676 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12878 BstLean.Part154.csC) ≤ 0.000993420377 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12878 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12878 BstLean.Part154.csC) (piBar (rhoBar 12878 BstLean.Part154.csC)) ≤ 0.000189683396 ∧
    cc1 (rhoBar 12878 BstLean.Part154.csC) (piBar (rhoBar 12878 BstLean.Part154.csC)) ≤ 0.000120696830 ∧
    cc2 (rhoBar 12878 BstLean.Part154.csC) ≤ 0.000070065465 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12878 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12878 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12878 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12878 BstLean.Part154.csC * nuR (rhoBar 12878 BstLean.Part154.csC)) ≤ 0.000496694771 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248339676 : ℝ) * 0.000993420377 := by gcongr
      _ ≤ (0.000496694771 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12878 BstLean.Part154.csC) * nuR (rhoBar 12878 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000993420377 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12878 BstLean.Part154.csC) * rhoBar 12878 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248339676 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248339676 / 2 + 0.399 * 0.000993420377 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189683396 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496694771 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120696830 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248339676 / 1.414213562 := by gcongr
      _ ≤ (0.000070065465 : ℝ) := by norm_num

end BstLean.Part269.N12878

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12878
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12878 BstLean.Part154.csC) (piBar (rhoBar 12878 BstLean.Part154.csC)) ≤ 1.55380E-7 := by
  have hr0 : 0 ≤ rhoBar 12878 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12878 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12878 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12878 BstLean.Part154.csC) (piBar (rhoBar 12878 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12878 BstLean.Part154.csC) (piBar (rhoBar 12878 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12878 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189683396 : ℝ) ^ 2 + 0.000120696830 ^ 2 + 3 * 0.000070065465 ^ 2 +
        2 * 0.797885 * 0.000189683396 * 0.000120696830 + 2 * 0.000189683396 * 0.000070065465 +
        4 * 0.797885 * 0.000120696830 * 0.000070065465 := by gcongr
    _ ≤ (1.55380E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12878 BstLean.Part154.csC Θ ≤ 0.002591698030 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12878 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12878 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12878 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12878 BstLean.Part154.csC) (piBar (rhoBar 12878 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12878 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035558712841 * 1.55380E-7 / (0.000248339291 : ℝ) := by gcongr
    _ ≤ 0.002591698030 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12878 BstLean.Part154.csC Θ ≤ 0.002874925069 + 0.000654878967 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12878 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12878 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12878 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035558712841 : ℝ) * ((2 * Θ * 0.000248339676 +
        (6863 / 10000) * 0.000248339676 * 12878 * 0.000993420377) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002874925069 + 0.000654878967 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12878 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12878 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12878 0.011 Θ ∧ gammaRatio 12878 0.011 Θ ≤ 0.000085372759 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12878 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035558712841 : ℝ) * 0.525 / ((1 - 0.011) * 12878) := by gcongr
      _ ≤ (0.000085372759 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12878 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12878 0.011 Θ) :=
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
    badAllowance 12878 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12878 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12878 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12878 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12878 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12878 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12878 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12878 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12878 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12878 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12878 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035558712841 : ℝ) * 12878 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12878 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003337961124 + 0.003246576997 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12878

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12878
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12878 BstLean.Part154.csC) (piBar (rhoBar 12878 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12878 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12878 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12878 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12878 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12878 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12878 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12878 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12878 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12878 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12878 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12878 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12878 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12878 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12878 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052116411560 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12878) ≤ 0.010523653093 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12878 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035558712841)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010523653093 + 2 * 0.737676 / 12878) := by gcongr
    _ ≤ (0.052116411560 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12878 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12878

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12878
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511506716 : ℝ) ≤ plow 12878 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12878) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052549014048)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360641466) : eMP 12878 0.011 xi bn ≤ 0.001171617764 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12878 : ℝ) * (1 - 0.011))) ≤ 0.000579327915 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001360641466 / (12878 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579327915 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579327915 : ℝ) + 3.141593 * 0.052549014048 / (12878 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001171617764 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052549014048)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360641466) : PiBarMP 12878 12 0.011 xi bn ≤ 0.160121453364 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12878 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036886873899 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.855403060730 : ℝ) ≤ √((12878 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.481275988596 : ℝ) ≤ √(12878 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12878) ≤ 0.122772749438 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036886873899 + 0.052549014048 * 1.772454 / (2 * (112.855403060730 : ℝ))) * (1 + 0.001171617764) +
        8 / (12878 * 113.481275988596) + 0.122772749438 := by gcongr
    _ ≤ (0.160121453364 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052549014048)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360641466) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281352128778) :
    parallelOracle 12878 0.011 xi bn cd ≤ 0.161097827322 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12878 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12878 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511506716 : ℝ) ≤ plow 12878 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.481275988596 : ℝ) ≤ √(12878 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281352128778 : ℝ) / (2 * 0.560511506716 * 113.481275988596)) * 0.160121453364 +
        0.281352128778 ^ 2 / (2 * 0.560511506716 * 113.481275988596) := by gcongr
    _ ≤ (0.161097827322 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052549014048) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360641466)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281352128778) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12878 12878 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511506716 : ℝ) ≤ plow 12878 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.481275988596 : ℝ) ≤ √(12878 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12878 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12878 Θ 1.22 ≤ 0.011685632617 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.481275988596 := by gcongr <;> linarith
      _ ≤ (0.011685632617 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12878 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12878 12878 0.011 ≤ 0.008423301289 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12878 12878 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12878 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12878 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12878 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12878 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161097827322 + 0.011685632617 + (0.008423301289 : ℝ) *
        (1 + 2 * (0.281352128778 + 0.011685632617) / (0.560511506716 * 113.481275988596))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12878]

end BstLean.Part269.N12878

/-! The original eight local profiles supply actual 12878 moment certificates. -/
namespace BstLean.Part269.N12878
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12878 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12878 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12878 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052549014048 ∧
    0 ≤ bN 12878 BstLean.Part154.csC (groupTheta g) ∧ bN 12878 BstLean.Part154.csC (groupTheta g) ≤ 0.001360641466 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12878 12878 0.011
      (momentAllowance 12878 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12878 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12878 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12878 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12878 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12878 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229235717218 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12878 0.011
      (momentAllowance 12878 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12878 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12878
/-! The actual computed-centre upper energy formula at 12878. -/
namespace BstLean.Part269.N12878
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12878

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12878
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12878)
open BstLean.Part268 (cell12878)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084987352142
  | 2 => 0.085921218103
  | 3 => 0.086851986138
  | 4 => 0.087780785299
  | 5 => 0.088708990111
  | 6 => 0.089638258158
  | 7 => 0.090570571404
  | 8 => 0.091508281361
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12878 12878 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12878 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12878

/-! Actual upper energy certificates on all 43 source endpoints at 12878. -/
namespace BstLean.Part269.N12878
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12878)
open BstLean.Part268 (cell12878)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12878 (gMinus 12878) (1 - (cell12878 i).lower) ≤ 1 ∧
    energyUpper 12878 (gMinus 12878) (BstLean.Part211.gPlus 12878)
      (finiteEnergy 12878 12878 0.011) (1 - (cell12878 i).lower) ≤
      (cell12878 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨10,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨11,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨12,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨13,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨14,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨15,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨16,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨17,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨18,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨19,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨20,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨21,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨22,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨23,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨24,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨25,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨26,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨27,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨28,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨29,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨30,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨31,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨32,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨33,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨34,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨35,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨36,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨37,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨38,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨39,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨40,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨41,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨42,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨43,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨44,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨45,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨46,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨47,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨48,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨49,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨50,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨51,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12878) (by norm_num)
        (q := 1 - (cell12878 ⟨52,by decide⟩).lower)
        (by norm_num [cell12878]) (by norm_num [cell12878])
      exact ⟨E.1,E.2.trans (by norm_num [cell12878])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12878

/-! Source-cell containment and simple scalar guards at 12878. -/
namespace BstLean.Part269.N12878
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12878)
open BstLean.Part268 (cell12878)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12878 ⟨10,by decide⟩).lower ∧ (cell12878 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12878 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12878 ⟨11,by decide⟩).lower ∧ (cell12878 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12878 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12878 ⟨12,by decide⟩).lower ∧ (cell12878 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12878 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12878 ⟨13,by decide⟩).lower ∧ (cell12878 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12878 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12878 ⟨14,by decide⟩).lower ∧ (cell12878 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12878 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12878 ⟨15,by decide⟩).lower ∧ (cell12878 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12878 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12878 ⟨16,by decide⟩).lower ∧ (cell12878 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12878 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12878 ⟨17,by decide⟩).lower ∧ (cell12878 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12878 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12878 ⟨18,by decide⟩).lower ∧ (cell12878 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12878 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12878 ⟨19,by decide⟩).lower ∧ (cell12878 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12878 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12878 ⟨20,by decide⟩).lower ∧ (cell12878 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12878 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12878 ⟨21,by decide⟩).lower ∧ (cell12878 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12878 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12878 ⟨22,by decide⟩).lower ∧ (cell12878 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12878 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12878 ⟨23,by decide⟩).lower ∧ (cell12878 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12878 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12878 ⟨24,by decide⟩).lower ∧ (cell12878 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12878 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12878 ⟨25,by decide⟩).lower ∧ (cell12878 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12878 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12878 ⟨26,by decide⟩).lower ∧ (cell12878 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12878 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12878 ⟨27,by decide⟩).lower ∧ (cell12878 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12878 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12878 ⟨28,by decide⟩).lower ∧ (cell12878 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12878 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12878 ⟨29,by decide⟩).lower ∧ (cell12878 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12878 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12878 ⟨30,by decide⟩).lower ∧ (cell12878 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12878 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12878 ⟨31,by decide⟩).lower ∧ (cell12878 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12878 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12878 ⟨32,by decide⟩).lower ∧ (cell12878 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12878 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12878 ⟨33,by decide⟩).lower ∧ (cell12878 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12878 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12878 ⟨34,by decide⟩).lower ∧ (cell12878 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12878 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12878 ⟨35,by decide⟩).lower ∧ (cell12878 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12878 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12878 ⟨36,by decide⟩).lower ∧ (cell12878 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12878 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12878 ⟨37,by decide⟩).lower ∧ (cell12878 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12878 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12878 ⟨38,by decide⟩).lower ∧ (cell12878 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12878 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12878 ⟨39,by decide⟩).lower ∧ (cell12878 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12878 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12878 ⟨40,by decide⟩).lower ∧ (cell12878 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12878 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12878 ⟨41,by decide⟩).lower ∧ (cell12878 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12878 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12878 ⟨42,by decide⟩).lower ∧ (cell12878 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12878 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12878 ⟨43,by decide⟩).lower ∧ (cell12878 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12878 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12878 ⟨44,by decide⟩).lower ∧ (cell12878 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12878 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12878 ⟨45,by decide⟩).lower ∧ (cell12878 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12878 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12878 ⟨46,by decide⟩).lower ∧ (cell12878 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12878 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12878 ⟨47,by decide⟩).lower ∧ (cell12878 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12878 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12878 ⟨48,by decide⟩).lower ∧ (cell12878 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12878 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12878 ⟨49,by decide⟩).lower ∧ (cell12878 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12878 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12878 ⟨50,by decide⟩).lower ∧ (cell12878 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12878 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12878 ⟨51,by decide⟩).lower ∧ (cell12878 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12878 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12878 ⟨52,by decide⟩).lower ∧ (cell12878 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12878 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12878 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12878 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12878,cell12878,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12878 i).lower ∧
    (cell12878 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12878 i).upper ≤ (0.532 : ℝ) ∧
    (cell12878 i).centre ≤ (0.1 : ℝ) ∧ (cell12878 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12878 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12878 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12878

/-! The local source numeric instances at 12878 have no network premises. -/
namespace BstLean.Part269.N12878
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12878)
open BstLean.Part268 (cell12878)

noncomputable def sourceNumerics12878 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12878 (cell12878 i)
      scalarRow12878.M scalarRow12878.H scalarRow12878.xi := by
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
    energy_allowance := scalarRow12878.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12878]
    centre_nonneg := (scalarRow12878.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12878])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12878
/-! Actual 12879 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12879
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12879 ≤ (1.035557320263 : ℝ) := by
  have hr : (113.485681916266 : ℝ) ≤ √(12879 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.485681916266 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12879 12879 (11 / 1000) ≤
    (0.008422974263 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12879) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.485681916266 : ℝ) ≤ √(12879 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12879)
  have hdiv : K / √(12879 : ℝ) ≤ K / 113.485681916266 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.485681916266 ≤ (0.008422974263 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12879.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12879 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12879 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12879 := gPlus_lower 12879
end BstLean.Part269.N12879

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12879
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035557320262 : ℝ) ≤ wn 12879 := by
  have hn : √(12879 : ℝ) ≤ 113.485681916267 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12879 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.485681916267 ≤ 2 / √(12879 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248319675 : ℝ) ≤ rhoBar 12879 BstLean.Part154.csC ∧
    rhoBar 12879 BstLean.Part154.csC ≤ 0.000248320059 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035557320262 : ℝ) / (1.295212 * 12879) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035557320263 : ℝ) / (1.29521 * 12879) := by gcongr
      _ ≤ (0.000248320059 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12879 BstLean.Part154.csC) ≤ 0.000993341899 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12879 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12879 BstLean.Part154.csC) (piBar (rhoBar 12879 BstLean.Part154.csC)) ≤ 0.000189668411 ∧
    cc1 (rhoBar 12879 BstLean.Part154.csC) (piBar (rhoBar 12879 BstLean.Part154.csC)) ≤ 0.000120687295 ∧
    cc2 (rhoBar 12879 BstLean.Part154.csC) ≤ 0.000070059931 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12879 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12879 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12879 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12879 BstLean.Part154.csC * nuR (rhoBar 12879 BstLean.Part154.csC)) ≤ 0.000496655534 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248320059 : ℝ) * 0.000993341899 := by gcongr
      _ ≤ (0.000496655534 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12879 BstLean.Part154.csC) * nuR (rhoBar 12879 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000993341899 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12879 BstLean.Part154.csC) * rhoBar 12879 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248320059 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248320059 / 2 + 0.399 * 0.000993341899 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189668411 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496655534 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120687295 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248320059 / 1.414213562 := by gcongr
      _ ≤ (0.000070059931 : ℝ) := by norm_num

end BstLean.Part269.N12879

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12879
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12879 BstLean.Part154.csC) (piBar (rhoBar 12879 BstLean.Part154.csC)) ≤ 1.55355E-7 := by
  have hr0 : 0 ≤ rhoBar 12879 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12879 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12879 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12879 BstLean.Part154.csC) (piBar (rhoBar 12879 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12879 BstLean.Part154.csC) (piBar (rhoBar 12879 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12879 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189668411 : ℝ) ^ 2 + 0.000120687295 ^ 2 + 3 * 0.000070059931 ^ 2 +
        2 * 0.797885 * 0.000189668411 * 0.000120687295 + 2 * 0.000189668411 * 0.000070059931 +
        4 * 0.797885 * 0.000120687295 * 0.000070059931 := by gcongr
    _ ≤ (1.55355E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12879 BstLean.Part154.csC Θ ≤ 0.002591482250 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12879 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12879 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12879 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12879 BstLean.Part154.csC) (piBar (rhoBar 12879 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12879 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035557320263 * 1.55355E-7 / (0.000248319675 : ℝ) := by gcongr
    _ ≤ 0.002591482250 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12879 BstLean.Part154.csC Θ ≤ 0.002874690219 + 0.000654826356 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12879 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12879 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12879 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035557320263 : ℝ) * ((2 * Θ * 0.000248320059 +
        (6863 / 10000) * 0.000248320059 * 12879 * 0.000993341899) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002874690219 + 0.000654826356 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12879 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12879 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12879 0.011 Θ ∧ gammaRatio 12879 0.011 Θ ≤ 0.000085366015 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12879 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035557320263 : ℝ) * 0.525 / ((1 - 0.011) * 12879) := by gcongr
      _ ≤ (0.000085366015 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12879 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12879 0.011 Θ) :=
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
    badAllowance 12879 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12879 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12879 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12879 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12879 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12879 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12879 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12879 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12879 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12879 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12879 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035557320263 : ℝ) * 12879 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12879 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003337726274 + 0.003246308606 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12879

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12879
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12879 BstLean.Part154.csC) (piBar (rhoBar 12879 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12879 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12879 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12879 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12879 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12879 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12879 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12879 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12879 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12879 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12879 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12879 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12879 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12879 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12879 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052114366425 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12879) ≤ 0.010523244527 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12879 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035557320263)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010523244527 + 2 * 0.737676 / 12879) := by gcongr
    _ ≤ (0.052114366425 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12879 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12879

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12879
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511550694 : ℝ) ≤ plow 12879 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12879) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052548638293)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360528182) : eMP 12879 0.011 xi bn ≤ 0.001171523449 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12879 : ℝ) * (1 - 0.011))) ≤ 0.000579281307 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001360528182 / (12879 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579281307 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579281307 : ℝ) + 3.141593 * 0.052548638293 / (12879 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001171523449 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052548638293)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360528182) : PiBarMP 12879 12 0.011 xi bn ≤ 0.160115126338 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12879 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036885338307 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.859784688789 : ℝ) ≤ √((12879 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.485681916266 : ℝ) ≤ √(12879 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12879) ≤ 0.122767982952 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036885338307 + 0.052548638293 * 1.772454 / (2 * (112.859784688789 : ℝ))) * (1 + 0.001171523449) +
        8 / (12879 * 113.485681916266) + 0.122767982952 := by gcongr
    _ ≤ (0.160115126338 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052548638293)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360528182) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281349264059) :
    parallelOracle 12879 0.011 xi bn cd ≤ 0.161091432045 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12879 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12879 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511550694 : ℝ) ≤ plow 12879 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.485681916266 : ℝ) ≤ √(12879 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281349264059 : ℝ) / (2 * 0.560511550694 * 113.485681916266)) * 0.160115126338 +
        0.281349264059 ^ 2 / (2 * 0.560511550694 * 113.485681916266) := by gcongr
    _ ≤ (0.161091432045 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052548638293) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360528182)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281349264059) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12879 12879 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511550694 : ℝ) ≤ plow 12879 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.485681916266 : ℝ) ≤ √(12879 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12879 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12879 Θ 1.22 ≤ 0.011685178938 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.485681916266 := by gcongr <;> linarith
      _ ≤ (0.011685178938 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12879 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12879 12879 0.011 ≤ 0.008422974263 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12879 12879 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12879 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12879 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12879 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12879 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161091432045 + 0.011685178938 + (0.008422974263 : ℝ) *
        (1 + 2 * (0.281349264059 + 0.011685178938) / (0.560511550694 * 113.485681916266))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12879]

end BstLean.Part269.N12879

/-! The original eight local profiles supply actual 12879 moment certificates. -/
namespace BstLean.Part269.N12879
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12879 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12879 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12879 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052548638293 ∧
    0 ≤ bN 12879 BstLean.Part154.csC (groupTheta g) ∧ bN 12879 BstLean.Part154.csC (groupTheta g) ≤ 0.001360528182 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12879 12879 0.011
      (momentAllowance 12879 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12879 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12879 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12879 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12879 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12879 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229234897634 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12879 0.011
      (momentAllowance 12879 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12879 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12879
/-! The actual computed-centre upper energy formula at 12879. -/
namespace BstLean.Part269.N12879
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12879

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12879
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12879)
open BstLean.Part268 (cell12879)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084984613106
  | 2 => 0.085918432581
  | 3 => 0.086849147981
  | 4 => 0.087777886901
  | 5 => 0.088706022146
  | 6 => 0.089635209277
  | 7 => 0.090567427905
  | 8 => 0.091505026810
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12879 12879 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12879 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12879

/-! Actual upper energy certificates on all 43 source endpoints at 12879. -/
namespace BstLean.Part269.N12879
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12879)
open BstLean.Part268 (cell12879)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12879 (gMinus 12879) (1 - (cell12879 i).lower) ≤ 1 ∧
    energyUpper 12879 (gMinus 12879) (BstLean.Part211.gPlus 12879)
      (finiteEnergy 12879 12879 0.011) (1 - (cell12879 i).lower) ≤
      (cell12879 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨10,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨11,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨12,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨13,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨14,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨15,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨16,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨17,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨18,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨19,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨20,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨21,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨22,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨23,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨24,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨25,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨26,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨27,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨28,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨29,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨30,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨31,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨32,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨33,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨34,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨35,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨36,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨37,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨38,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨39,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨40,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨41,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨42,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨43,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨44,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨45,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨46,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨47,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨48,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨49,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨50,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨51,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12879) (by norm_num)
        (q := 1 - (cell12879 ⟨52,by decide⟩).lower)
        (by norm_num [cell12879]) (by norm_num [cell12879])
      exact ⟨E.1,E.2.trans (by norm_num [cell12879])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12879

/-! Source-cell containment and simple scalar guards at 12879. -/
namespace BstLean.Part269.N12879
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12879)
open BstLean.Part268 (cell12879)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12879 ⟨10,by decide⟩).lower ∧ (cell12879 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12879 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12879 ⟨11,by decide⟩).lower ∧ (cell12879 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12879 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12879 ⟨12,by decide⟩).lower ∧ (cell12879 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12879 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12879 ⟨13,by decide⟩).lower ∧ (cell12879 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12879 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12879 ⟨14,by decide⟩).lower ∧ (cell12879 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12879 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12879 ⟨15,by decide⟩).lower ∧ (cell12879 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12879 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12879 ⟨16,by decide⟩).lower ∧ (cell12879 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12879 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12879 ⟨17,by decide⟩).lower ∧ (cell12879 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12879 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12879 ⟨18,by decide⟩).lower ∧ (cell12879 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12879 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12879 ⟨19,by decide⟩).lower ∧ (cell12879 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12879 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12879 ⟨20,by decide⟩).lower ∧ (cell12879 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12879 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12879 ⟨21,by decide⟩).lower ∧ (cell12879 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12879 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12879 ⟨22,by decide⟩).lower ∧ (cell12879 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12879 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12879 ⟨23,by decide⟩).lower ∧ (cell12879 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12879 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12879 ⟨24,by decide⟩).lower ∧ (cell12879 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12879 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12879 ⟨25,by decide⟩).lower ∧ (cell12879 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12879 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12879 ⟨26,by decide⟩).lower ∧ (cell12879 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12879 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12879 ⟨27,by decide⟩).lower ∧ (cell12879 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12879 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12879 ⟨28,by decide⟩).lower ∧ (cell12879 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12879 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12879 ⟨29,by decide⟩).lower ∧ (cell12879 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12879 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12879 ⟨30,by decide⟩).lower ∧ (cell12879 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12879 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12879 ⟨31,by decide⟩).lower ∧ (cell12879 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12879 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12879 ⟨32,by decide⟩).lower ∧ (cell12879 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12879 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12879 ⟨33,by decide⟩).lower ∧ (cell12879 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12879 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12879 ⟨34,by decide⟩).lower ∧ (cell12879 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12879 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12879 ⟨35,by decide⟩).lower ∧ (cell12879 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12879 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12879 ⟨36,by decide⟩).lower ∧ (cell12879 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12879 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12879 ⟨37,by decide⟩).lower ∧ (cell12879 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12879 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12879 ⟨38,by decide⟩).lower ∧ (cell12879 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12879 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12879 ⟨39,by decide⟩).lower ∧ (cell12879 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12879 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12879 ⟨40,by decide⟩).lower ∧ (cell12879 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12879 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12879 ⟨41,by decide⟩).lower ∧ (cell12879 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12879 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12879 ⟨42,by decide⟩).lower ∧ (cell12879 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12879 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12879 ⟨43,by decide⟩).lower ∧ (cell12879 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12879 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12879 ⟨44,by decide⟩).lower ∧ (cell12879 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12879 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12879 ⟨45,by decide⟩).lower ∧ (cell12879 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12879 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12879 ⟨46,by decide⟩).lower ∧ (cell12879 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12879 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12879 ⟨47,by decide⟩).lower ∧ (cell12879 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12879 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12879 ⟨48,by decide⟩).lower ∧ (cell12879 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12879 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12879 ⟨49,by decide⟩).lower ∧ (cell12879 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12879 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12879 ⟨50,by decide⟩).lower ∧ (cell12879 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12879 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12879 ⟨51,by decide⟩).lower ∧ (cell12879 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12879 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12879 ⟨52,by decide⟩).lower ∧ (cell12879 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12879 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12879 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12879 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12879,cell12879,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12879 i).lower ∧
    (cell12879 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12879 i).upper ≤ (0.532 : ℝ) ∧
    (cell12879 i).centre ≤ (0.1 : ℝ) ∧ (cell12879 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12879 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12879 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12879

/-! The local source numeric instances at 12879 have no network premises. -/
namespace BstLean.Part269.N12879
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12879)
open BstLean.Part268 (cell12879)

noncomputable def sourceNumerics12879 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12879 (cell12879 i)
      scalarRow12879.M scalarRow12879.H scalarRow12879.xi := by
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
    energy_allowance := scalarRow12879.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12879]
    centre_nonneg := (scalarRow12879.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12879])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12879
/-! Actual 12880 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12880
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12880 ≤ (1.035555927849 : ℝ) := by
  have hr : (113.490087672888 : ℝ) ≤ √(12880 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.490087672888 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12880 12880 (11 / 1000) ≤
    (0.008422647276 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12880) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.490087672888 : ℝ) ≤ √(12880 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12880)
  have hdiv : K / √(12880 : ℝ) ≤ K / 113.490087672888 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.490087672888 ≤ (0.008422647276 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12880.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12880 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12880 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12880 := gPlus_lower 12880
end BstLean.Part269.N12880

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12880
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035555927848 : ℝ) ≤ wn 12880 := by
  have hn : √(12880 : ℝ) ≤ 113.490087672889 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12880 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.490087672889 ≤ 2 / √(12880 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248300061 : ℝ) ≤ rhoBar 12880 BstLean.Part154.csC ∧
    rhoBar 12880 BstLean.Part154.csC ≤ 0.000248300446 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035555927848 : ℝ) / (1.295212 * 12880) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035555927849 : ℝ) / (1.29521 * 12880) := by gcongr
      _ ≤ (0.000248300446 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12880 BstLean.Part154.csC) ≤ 0.000993263438 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12880 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12880 BstLean.Part154.csC) (piBar (rhoBar 12880 BstLean.Part154.csC)) ≤ 0.000189653430 ∧
    cc1 (rhoBar 12880 BstLean.Part154.csC) (piBar (rhoBar 12880 BstLean.Part154.csC)) ≤ 0.000120677763 ∧
    cc2 (rhoBar 12880 BstLean.Part154.csC) ≤ 0.000070054397 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12880 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12880 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12880 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12880 BstLean.Part154.csC * nuR (rhoBar 12880 BstLean.Part154.csC)) ≤ 0.000496616306 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248300446 : ℝ) * 0.000993263438 := by gcongr
      _ ≤ (0.000496616306 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12880 BstLean.Part154.csC) * nuR (rhoBar 12880 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000993263438 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12880 BstLean.Part154.csC) * rhoBar 12880 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248300446 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248300446 / 2 + 0.399 * 0.000993263438 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189653430 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496616306 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120677763 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248300446 / 1.414213562 := by gcongr
      _ ≤ (0.000070054397 : ℝ) := by norm_num

end BstLean.Part269.N12880

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12880
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12880 BstLean.Part154.csC) (piBar (rhoBar 12880 BstLean.Part154.csC)) ≤ 1.55331E-7 := by
  have hr0 : 0 ≤ rhoBar 12880 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12880 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12880 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12880 BstLean.Part154.csC) (piBar (rhoBar 12880 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12880 BstLean.Part154.csC) (piBar (rhoBar 12880 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12880 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189653430 : ℝ) ^ 2 + 0.000120677763 ^ 2 + 3 * 0.000070054397 ^ 2 +
        2 * 0.797885 * 0.000189653430 * 0.000120677763 + 2 * 0.000189653430 * 0.000070054397 +
        4 * 0.797885 * 0.000120677763 * 0.000070054397 := by gcongr
    _ ≤ (1.55331E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12880 BstLean.Part154.csC Θ ≤ 0.002591283099 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12880 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12880 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12880 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12880 BstLean.Part154.csC) (piBar (rhoBar 12880 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12880 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035555927849 * 1.55331E-7 / (0.000248300061 : ℝ) := by gcongr
    _ ≤ 0.002591283099 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12880 BstLean.Part154.csC Θ ≤ 0.002874455430 + 0.000654773755 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12880 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12880 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12880 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035555927849 : ℝ) * ((2 * Θ * 0.000248300446 +
        (6863 / 10000) * 0.000248300446 * 12880 * 0.000993263438) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002874455430 + 0.000654773755 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12880 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12880 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12880 0.011 Θ ∧ gammaRatio 12880 0.011 Θ ≤ 0.000085359273 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12880 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035555927849 : ℝ) * 0.525 / ((1 - 0.011) * 12880) := by gcongr
      _ ≤ (0.000085359273 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12880 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12880 0.011 Θ) :=
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
    badAllowance 12880 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12880 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12880 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12880 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12880 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12880 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12880 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12880 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12880 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12880 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12880 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035555927849 : ℝ) * 12880 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12880 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003337491485 + 0.003246056854 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12880

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12880
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12880 BstLean.Part154.csC) (piBar (rhoBar 12880 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12880 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12880 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12880 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12880 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12880 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12880 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12880 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12880 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12880 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12880 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12880 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12880 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12880 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12880 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052112321527 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12880) ≤ 0.010522836008 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12880 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035555927849)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010522836008 + 2 * 0.737676 / 12880) := by gcongr
    _ ≤ (0.052112321527 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12880 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12880

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12880
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511594666 : ℝ) ≤ plow 12880 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12880) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052548271334)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360423627) : eMP 12880 0.011 xi bn ≤ 0.001171432860 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12880 : ℝ) * (1 - 0.011))) ≤ 0.000579236561 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001360423627 / (12880 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579236561 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579236561 : ℝ) + 3.141593 * 0.052548271334 / (12880 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001171432860 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052548271334)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360423627) : PiBarMP 12880 12 0.011 xi bn ≤ 0.160108918484 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12880 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036883920982 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.864166146744 : ℝ) ≤ √((12880 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.490087672888 : ℝ) ≤ √(12880 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12880) ≤ 0.122763217022 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036883920982 + 0.052548271334 * 1.772454 / (2 * (112.864166146744 : ℝ))) * (1 + 0.001171432860) +
        8 / (12880 * 113.490087672888) + 0.122763217022 := by gcongr
    _ ≤ (0.160108918484 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052548271334)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360423627) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281346418760) :
    parallelOracle 12880 0.011 xi bn cd ≤ 0.161085156320 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12880 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12880 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511594666 : ℝ) ≤ plow 12880 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.490087672888 : ℝ) ≤ √(12880 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281346418760 : ℝ) / (2 * 0.560511594666 * 113.490087672888)) * 0.160108918484 +
        0.281346418760 ^ 2 / (2 * 0.560511594666 * 113.490087672888) := by gcongr
    _ ≤ (0.161085156320 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052548271334) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360423627)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281346418760) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12880 12880 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511594666 : ℝ) ≤ plow 12880 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.490087672888 : ℝ) ≤ √(12880 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12880 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12880 Θ 1.22 ≤ 0.011684725312 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.490087672888 := by gcongr <;> linarith
      _ ≤ (0.011684725312 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12880 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12880 12880 0.011 ≤ 0.008422647276 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12880 12880 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12880 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12880 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12880 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12880 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161085156320 + 0.011684725312 + (0.008422647276 : ℝ) *
        (1 + 2 * (0.281346418760 + 0.011684725312) / (0.560511594666 * 113.490087672888))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12880]

end BstLean.Part269.N12880

/-! The original eight local profiles supply actual 12880 moment certificates. -/
namespace BstLean.Part269.N12880
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12880 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12880 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12880 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052548271334 ∧
    0 ≤ bN 12880 BstLean.Part154.csC (groupTheta g) ∧ bN 12880 BstLean.Part154.csC (groupTheta g) ≤ 0.001360423627 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12880 12880 0.011
      (momentAllowance 12880 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12880 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12880 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12880 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12880 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12880 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229234097233 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12880 0.011
      (momentAllowance 12880 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12880 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12880
/-! The actual computed-centre upper energy formula at 12880. -/
namespace BstLean.Part269.N12880
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12880

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12880
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12880)
open BstLean.Part268 (cell12880)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084981874979
  | 2 => 0.085915648003
  | 3 => 0.086846310811
  | 4 => 0.087774989544
  | 5 => 0.088703055287
  | 6 => 0.089632161582
  | 7 => 0.090564285689
  | 8 => 0.091501773661
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12880 12880 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12880 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12880

/-! Actual upper energy certificates on all 43 source endpoints at 12880. -/
namespace BstLean.Part269.N12880
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12880)
open BstLean.Part268 (cell12880)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12880 (gMinus 12880) (1 - (cell12880 i).lower) ≤ 1 ∧
    energyUpper 12880 (gMinus 12880) (BstLean.Part211.gPlus 12880)
      (finiteEnergy 12880 12880 0.011) (1 - (cell12880 i).lower) ≤
      (cell12880 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨10,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨11,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨12,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨13,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨14,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨15,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨16,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨17,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨18,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨19,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨20,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨21,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨22,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨23,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨24,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨25,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨26,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨27,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨28,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨29,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨30,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨31,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨32,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨33,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨34,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨35,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨36,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨37,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨38,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨39,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨40,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨41,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨42,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨43,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨44,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨45,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨46,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨47,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨48,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨49,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨50,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨51,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12880) (by norm_num)
        (q := 1 - (cell12880 ⟨52,by decide⟩).lower)
        (by norm_num [cell12880]) (by norm_num [cell12880])
      exact ⟨E.1,E.2.trans (by norm_num [cell12880])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12880

/-! Source-cell containment and simple scalar guards at 12880. -/
namespace BstLean.Part269.N12880
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12880)
open BstLean.Part268 (cell12880)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12880 ⟨10,by decide⟩).lower ∧ (cell12880 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12880 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12880 ⟨11,by decide⟩).lower ∧ (cell12880 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12880 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12880 ⟨12,by decide⟩).lower ∧ (cell12880 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12880 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12880 ⟨13,by decide⟩).lower ∧ (cell12880 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12880 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12880 ⟨14,by decide⟩).lower ∧ (cell12880 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12880 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12880 ⟨15,by decide⟩).lower ∧ (cell12880 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12880 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12880 ⟨16,by decide⟩).lower ∧ (cell12880 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12880 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12880 ⟨17,by decide⟩).lower ∧ (cell12880 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12880 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12880 ⟨18,by decide⟩).lower ∧ (cell12880 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12880 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12880 ⟨19,by decide⟩).lower ∧ (cell12880 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12880 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12880 ⟨20,by decide⟩).lower ∧ (cell12880 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12880 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12880 ⟨21,by decide⟩).lower ∧ (cell12880 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12880 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12880 ⟨22,by decide⟩).lower ∧ (cell12880 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12880 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12880 ⟨23,by decide⟩).lower ∧ (cell12880 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12880 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12880 ⟨24,by decide⟩).lower ∧ (cell12880 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12880 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12880 ⟨25,by decide⟩).lower ∧ (cell12880 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12880 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12880 ⟨26,by decide⟩).lower ∧ (cell12880 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12880 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12880 ⟨27,by decide⟩).lower ∧ (cell12880 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12880 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12880 ⟨28,by decide⟩).lower ∧ (cell12880 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12880 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12880 ⟨29,by decide⟩).lower ∧ (cell12880 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12880 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12880 ⟨30,by decide⟩).lower ∧ (cell12880 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12880 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12880 ⟨31,by decide⟩).lower ∧ (cell12880 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12880 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12880 ⟨32,by decide⟩).lower ∧ (cell12880 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12880 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12880 ⟨33,by decide⟩).lower ∧ (cell12880 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12880 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12880 ⟨34,by decide⟩).lower ∧ (cell12880 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12880 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12880 ⟨35,by decide⟩).lower ∧ (cell12880 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12880 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12880 ⟨36,by decide⟩).lower ∧ (cell12880 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12880 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12880 ⟨37,by decide⟩).lower ∧ (cell12880 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12880 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12880 ⟨38,by decide⟩).lower ∧ (cell12880 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12880 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12880 ⟨39,by decide⟩).lower ∧ (cell12880 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12880 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12880 ⟨40,by decide⟩).lower ∧ (cell12880 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12880 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12880 ⟨41,by decide⟩).lower ∧ (cell12880 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12880 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12880 ⟨42,by decide⟩).lower ∧ (cell12880 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12880 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12880 ⟨43,by decide⟩).lower ∧ (cell12880 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12880 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12880 ⟨44,by decide⟩).lower ∧ (cell12880 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12880 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12880 ⟨45,by decide⟩).lower ∧ (cell12880 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12880 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12880 ⟨46,by decide⟩).lower ∧ (cell12880 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12880 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12880 ⟨47,by decide⟩).lower ∧ (cell12880 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12880 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12880 ⟨48,by decide⟩).lower ∧ (cell12880 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12880 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12880 ⟨49,by decide⟩).lower ∧ (cell12880 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12880 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12880 ⟨50,by decide⟩).lower ∧ (cell12880 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12880 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12880 ⟨51,by decide⟩).lower ∧ (cell12880 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12880 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12880 ⟨52,by decide⟩).lower ∧ (cell12880 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12880 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12880 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12880 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12880,cell12880,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12880 i).lower ∧
    (cell12880 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12880 i).upper ≤ (0.532 : ℝ) ∧
    (cell12880 i).centre ≤ (0.1 : ℝ) ∧ (cell12880 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12880 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12880 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12880

/-! The local source numeric instances at 12880 have no network premises. -/
namespace BstLean.Part269.N12880
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12880)
open BstLean.Part268 (cell12880)

noncomputable def sourceNumerics12880 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12880 (cell12880 i)
      scalarRow12880.M scalarRow12880.H scalarRow12880.xi := by
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
    energy_allowance := scalarRow12880.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12880]
    centre_nonneg := (scalarRow12880.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12880])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12880
/-! Actual 12881 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12881
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12881 ≤ (1.035554535598 : ℝ) := by
  have hr : (113.494493258483 : ℝ) ≤ √(12881 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.494493258483 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12881 12881 (11 / 1000) ≤
    (0.008422320326 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12881) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.494493258483 : ℝ) ≤ √(12881 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12881)
  have hdiv : K / √(12881 : ℝ) ≤ K / 113.494493258483 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.494493258483 ≤ (0.008422320326 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12881.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12881 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12881 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12881 := gPlus_lower 12881
end BstLean.Part269.N12881

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12881
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035554535597 : ℝ) ≤ wn 12881 := by
  have hn : √(12881 : ℝ) ≤ 113.494493258484 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12881 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.494493258484 ≤ 2 / √(12881 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248280451 : ℝ) ≤ rhoBar 12881 BstLean.Part154.csC ∧
    rhoBar 12881 BstLean.Part154.csC ≤ 0.000248280836 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035554535597 : ℝ) / (1.295212 * 12881) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035554535598 : ℝ) / (1.29521 * 12881) := by gcongr
      _ ≤ (0.000248280836 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12881 BstLean.Part154.csC) ≤ 0.000993184988 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12881 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12881 BstLean.Part154.csC) (piBar (rhoBar 12881 BstLean.Part154.csC)) ≤ 0.000189638451 ∧
    cc1 (rhoBar 12881 BstLean.Part154.csC) (piBar (rhoBar 12881 BstLean.Part154.csC)) ≤ 0.000120668232 ∧
    cc2 (rhoBar 12881 BstLean.Part154.csC) ≤ 0.000070048865 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12881 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12881 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12881 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12881 BstLean.Part154.csC * nuR (rhoBar 12881 BstLean.Part154.csC)) ≤ 0.000496577083 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248280836 : ℝ) * 0.000993184988 := by gcongr
      _ ≤ (0.000496577083 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12881 BstLean.Part154.csC) * nuR (rhoBar 12881 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000993184988 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12881 BstLean.Part154.csC) * rhoBar 12881 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248280836 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248280836 / 2 + 0.399 * 0.000993184988 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189638451 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496577083 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120668232 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248280836 / 1.414213562 := by gcongr
      _ ≤ (0.000070048865 : ℝ) := by norm_num

end BstLean.Part269.N12881

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12881
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12881 BstLean.Part154.csC) (piBar (rhoBar 12881 BstLean.Part154.csC)) ≤ 1.55306E-7 := by
  have hr0 : 0 ≤ rhoBar 12881 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12881 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12881 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12881 BstLean.Part154.csC) (piBar (rhoBar 12881 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12881 BstLean.Part154.csC) (piBar (rhoBar 12881 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12881 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189638451 : ℝ) ^ 2 + 0.000120668232 ^ 2 + 3 * 0.000070048865 ^ 2 +
        2 * 0.797885 * 0.000189638451 * 0.000120668232 + 2 * 0.000189638451 * 0.000070048865 +
        4 * 0.797885 * 0.000120668232 * 0.000070048865 := by gcongr
    _ ≤ (1.55306E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12881 BstLean.Part154.csC Θ ≤ 0.002591067192 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12881 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12881 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12881 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12881 BstLean.Part154.csC) (piBar (rhoBar 12881 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12881 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035554535598 * 1.55306E-7 / (0.000248280451 : ℝ) := by gcongr
    _ ≤ 0.002591067192 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12881 BstLean.Part154.csC Θ ≤ 0.002874220674 + 0.000654721163 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12881 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12881 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12881 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035554535598 : ℝ) * ((2 * Θ * 0.000248280836 +
        (6863 / 10000) * 0.000248280836 * 12881 * 0.000993184988) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002874220674 + 0.000654721163 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12881 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12881 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12881 0.011 Θ ∧ gammaRatio 12881 0.011 Θ ≤ 0.000085352531 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12881 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035554535598 : ℝ) * 0.525 / ((1 - 0.011) * 12881) := by gcongr
      _ ≤ (0.000085352531 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12881 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12881 0.011 Θ) :=
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
    badAllowance 12881 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12881 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12881 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12881 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12881 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12881 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12881 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12881 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12881 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12881 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12881 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035554535598 : ℝ) * 12881 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12881 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003337256729 + 0.003245788355 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12881

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12881
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12881 BstLean.Part154.csC) (piBar (rhoBar 12881 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12881 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12881 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12881 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12881 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12881 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12881 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12881 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12881 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12881 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12881 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12881 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12881 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12881 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12881 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052110276871 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12881) ≤ 0.010522427537 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12881 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035554535598)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010522427537 + 2 * 0.737676 / 12881) := by gcongr
    _ ≤ (0.052110276871 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12881 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12881

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12881
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511638630 : ℝ) ≤ plow 12881 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12881) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052547895616)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360310276) : eMP 12881 0.011 xi bn ≤ 0.001171338531 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12881 : ℝ) * (1 - 0.011))) ≤ 0.000579189946 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001360310276 / (12881 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579189946 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579189946 : ℝ) + 3.141593 * 0.052547895616 / (12881 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001171338531 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052547895616)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360310276) : PiBarMP 12881 12 0.011 xi bn ≤ 0.160102591540 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12881 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036882384359 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.868547434615 : ℝ) ≤ √((12881 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.494493258483 : ℝ) ≤ √(12881 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12881) ≤ 0.122758451646 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036882384359 + 0.052547895616 * 1.772454 / (2 * (112.868547434615 : ℝ))) * (1 + 0.001171338531) +
        8 / (12881 * 113.494493258483) + 0.122758451646 := by gcongr
    _ ≤ (0.160102591540 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052547895616)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360310276) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281343554595) :
    parallelOracle 12881 0.011 xi bn cd ≤ 0.161078761142 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12881 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12881 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511638630 : ℝ) ≤ plow 12881 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.494493258483 : ℝ) ≤ √(12881 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281343554595 : ℝ) / (2 * 0.560511638630 * 113.494493258483)) * 0.160102591540 +
        0.281343554595 ^ 2 / (2 * 0.560511638630 * 113.494493258483) := by gcongr
    _ ≤ (0.161078761142 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052547895616) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360310276)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281343554595) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12881 12881 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511638630 : ℝ) ≤ plow 12881 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.494493258483 : ℝ) ≤ √(12881 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12881 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12881 Θ 1.22 ≤ 0.011684271739 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.494493258483 := by gcongr <;> linarith
      _ ≤ (0.011684271739 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12881 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12881 12881 0.011 ≤ 0.008422320326 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12881 12881 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12881 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12881 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12881 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12881 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161078761142 + 0.011684271739 + (0.008422320326 : ℝ) *
        (1 + 2 * (0.281343554595 + 0.011684271739) / (0.560511638630 * 113.494493258483))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12881]

end BstLean.Part269.N12881

/-! The original eight local profiles supply actual 12881 moment certificates. -/
namespace BstLean.Part269.N12881
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12881 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12881 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12881 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052547895616 ∧
    0 ≤ bN 12881 BstLean.Part154.csC (groupTheta g) ∧ bN 12881 BstLean.Part154.csC (groupTheta g) ≤ 0.001360310276 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12881 12881 0.011
      (momentAllowance 12881 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12881 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12881 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12881 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12881 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12881 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229233277724 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12881 0.011
      (momentAllowance 12881 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12881 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12881
/-! The actual computed-centre upper energy formula at 12881. -/
namespace BstLean.Part269.N12881
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12881

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12881
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12881)
open BstLean.Part268 (cell12881)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084979137759
  | 2 => 0.085912864367
  | 3 => 0.086843474628
  | 4 => 0.087772093228
  | 5 => 0.088700089534
  | 6 => 0.089629115074
  | 7 => 0.090561144755
  | 8 => 0.091498521910
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12881 12881 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12881 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12881

/-! Actual upper energy certificates on all 43 source endpoints at 12881. -/
namespace BstLean.Part269.N12881
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12881)
open BstLean.Part268 (cell12881)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12881 (gMinus 12881) (1 - (cell12881 i).lower) ≤ 1 ∧
    energyUpper 12881 (gMinus 12881) (BstLean.Part211.gPlus 12881)
      (finiteEnergy 12881 12881 0.011) (1 - (cell12881 i).lower) ≤
      (cell12881 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨10,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨11,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨12,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨13,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨14,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨15,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨16,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨17,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨18,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨19,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨20,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨21,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨22,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨23,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨24,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨25,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨26,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨27,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨28,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨29,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨30,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨31,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨32,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨33,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨34,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨35,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨36,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨37,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨38,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨39,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨40,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨41,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨42,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨43,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨44,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨45,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨46,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨47,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨48,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨49,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨50,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨51,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12881) (by norm_num)
        (q := 1 - (cell12881 ⟨52,by decide⟩).lower)
        (by norm_num [cell12881]) (by norm_num [cell12881])
      exact ⟨E.1,E.2.trans (by norm_num [cell12881])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12881

/-! Source-cell containment and simple scalar guards at 12881. -/
namespace BstLean.Part269.N12881
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12881)
open BstLean.Part268 (cell12881)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12881 ⟨10,by decide⟩).lower ∧ (cell12881 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12881 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12881 ⟨11,by decide⟩).lower ∧ (cell12881 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12881 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12881 ⟨12,by decide⟩).lower ∧ (cell12881 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12881 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12881 ⟨13,by decide⟩).lower ∧ (cell12881 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12881 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12881 ⟨14,by decide⟩).lower ∧ (cell12881 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12881 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12881 ⟨15,by decide⟩).lower ∧ (cell12881 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12881 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12881 ⟨16,by decide⟩).lower ∧ (cell12881 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12881 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12881 ⟨17,by decide⟩).lower ∧ (cell12881 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12881 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12881 ⟨18,by decide⟩).lower ∧ (cell12881 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12881 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12881 ⟨19,by decide⟩).lower ∧ (cell12881 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12881 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12881 ⟨20,by decide⟩).lower ∧ (cell12881 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12881 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12881 ⟨21,by decide⟩).lower ∧ (cell12881 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12881 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12881 ⟨22,by decide⟩).lower ∧ (cell12881 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12881 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12881 ⟨23,by decide⟩).lower ∧ (cell12881 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12881 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12881 ⟨24,by decide⟩).lower ∧ (cell12881 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12881 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12881 ⟨25,by decide⟩).lower ∧ (cell12881 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12881 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12881 ⟨26,by decide⟩).lower ∧ (cell12881 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12881 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12881 ⟨27,by decide⟩).lower ∧ (cell12881 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12881 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12881 ⟨28,by decide⟩).lower ∧ (cell12881 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12881 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12881 ⟨29,by decide⟩).lower ∧ (cell12881 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12881 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12881 ⟨30,by decide⟩).lower ∧ (cell12881 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12881 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12881 ⟨31,by decide⟩).lower ∧ (cell12881 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12881 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12881 ⟨32,by decide⟩).lower ∧ (cell12881 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12881 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12881 ⟨33,by decide⟩).lower ∧ (cell12881 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12881 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12881 ⟨34,by decide⟩).lower ∧ (cell12881 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12881 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12881 ⟨35,by decide⟩).lower ∧ (cell12881 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12881 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12881 ⟨36,by decide⟩).lower ∧ (cell12881 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12881 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12881 ⟨37,by decide⟩).lower ∧ (cell12881 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12881 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12881 ⟨38,by decide⟩).lower ∧ (cell12881 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12881 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12881 ⟨39,by decide⟩).lower ∧ (cell12881 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12881 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12881 ⟨40,by decide⟩).lower ∧ (cell12881 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12881 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12881 ⟨41,by decide⟩).lower ∧ (cell12881 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12881 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12881 ⟨42,by decide⟩).lower ∧ (cell12881 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12881 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12881 ⟨43,by decide⟩).lower ∧ (cell12881 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12881 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12881 ⟨44,by decide⟩).lower ∧ (cell12881 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12881 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12881 ⟨45,by decide⟩).lower ∧ (cell12881 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12881 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12881 ⟨46,by decide⟩).lower ∧ (cell12881 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12881 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12881 ⟨47,by decide⟩).lower ∧ (cell12881 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12881 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12881 ⟨48,by decide⟩).lower ∧ (cell12881 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12881 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12881 ⟨49,by decide⟩).lower ∧ (cell12881 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12881 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12881 ⟨50,by decide⟩).lower ∧ (cell12881 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12881 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12881 ⟨51,by decide⟩).lower ∧ (cell12881 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12881 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12881 ⟨52,by decide⟩).lower ∧ (cell12881 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12881 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12881 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12881 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12881,cell12881,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12881 i).lower ∧
    (cell12881 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12881 i).upper ≤ (0.532 : ℝ) ∧
    (cell12881 i).centre ≤ (0.1 : ℝ) ∧ (cell12881 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12881 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12881 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12881

/-! The local source numeric instances at 12881 have no network premises. -/
namespace BstLean.Part269.N12881
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12881)
open BstLean.Part268 (cell12881)

noncomputable def sourceNumerics12881 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12881 (cell12881 i)
      scalarRow12881.M scalarRow12881.H scalarRow12881.xi := by
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
    energy_allowance := scalarRow12881.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12881]
    centre_nonneg := (scalarRow12881.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12881])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12881
/-! Actual 12882 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12882
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12882 ≤ (1.035553143510 : ℝ) := by
  have hr : (113.498898673070 : ℝ) ≤ √(12882 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.498898673070 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12882 12882 (11 / 1000) ≤
    (0.008421993415 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12882) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.498898673070 : ℝ) ≤ √(12882 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12882)
  have hdiv : K / √(12882 : ℝ) ≤ K / 113.498898673070 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.498898673070 ≤ (0.008421993415 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12882.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12882 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12882 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12882 := gPlus_lower 12882
end BstLean.Part269.N12882

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12882
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035553143509 : ℝ) ≤ wn 12882 := by
  have hn : √(12882 : ℝ) ≤ 113.498898673071 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12882 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.498898673071 ≤ 2 / √(12882 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248260844 : ℝ) ≤ rhoBar 12882 BstLean.Part154.csC ∧
    rhoBar 12882 BstLean.Part154.csC ≤ 0.000248261228 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035553143509 : ℝ) / (1.295212 * 12882) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035553143510 : ℝ) / (1.29521 * 12882) := by gcongr
      _ ≤ (0.000248261228 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12882 BstLean.Part154.csC) ≤ 0.000993106546 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12882 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12882 BstLean.Part154.csC) (piBar (rhoBar 12882 BstLean.Part154.csC)) ≤ 0.000189623474 ∧
    cc1 (rhoBar 12882 BstLean.Part154.csC) (piBar (rhoBar 12882 BstLean.Part154.csC)) ≤ 0.000120658702 ∧
    cc2 (rhoBar 12882 BstLean.Part154.csC) ≤ 0.000070043332 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12882 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12882 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12882 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12882 BstLean.Part154.csC * nuR (rhoBar 12882 BstLean.Part154.csC)) ≤ 0.000496537865 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248261228 : ℝ) * 0.000993106546 := by gcongr
      _ ≤ (0.000496537865 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12882 BstLean.Part154.csC) * nuR (rhoBar 12882 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000993106546 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12882 BstLean.Part154.csC) * rhoBar 12882 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248261228 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248261228 / 2 + 0.399 * 0.000993106546 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189623474 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496537865 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120658702 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248261228 / 1.414213562 := by gcongr
      _ ≤ (0.000070043332 : ℝ) := by norm_num

end BstLean.Part269.N12882

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12882
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12882 BstLean.Part154.csC) (piBar (rhoBar 12882 BstLean.Part154.csC)) ≤ 1.55282E-7 := by
  have hr0 : 0 ≤ rhoBar 12882 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12882 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12882 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12882 BstLean.Part154.csC) (piBar (rhoBar 12882 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12882 BstLean.Part154.csC) (piBar (rhoBar 12882 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12882 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189623474 : ℝ) ^ 2 + 0.000120658702 ^ 2 + 3 * 0.000070043332 ^ 2 +
        2 * 0.797885 * 0.000189623474 * 0.000120658702 + 2 * 0.000189623474 * 0.000070043332 +
        4 * 0.797885 * 0.000120658702 * 0.000070043332 := by gcongr
    _ ≤ (1.55282E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12882 BstLean.Part154.csC Θ ≤ 0.002590867906 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12882 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12882 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12882 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12882 BstLean.Part154.csC) (piBar (rhoBar 12882 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12882 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035553143510 * 1.55282E-7 / (0.000248260844 : ℝ) := by gcongr
    _ ≤ 0.002590867906 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12882 BstLean.Part154.csC Θ ≤ 0.002873985932 + 0.000654668576 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12882 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12882 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12882 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035553143510 : ℝ) * ((2 * Θ * 0.000248261228 +
        (6863 / 10000) * 0.000248261228 * 12882 * 0.000993106546) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002873985932 + 0.000654668576 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12882 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12882 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12882 0.011 Θ ∧ gammaRatio 12882 0.011 Θ ≤ 0.000085345791 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12882 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035553143510 : ℝ) * 0.525 / ((1 - 0.011) * 12882) := by gcongr
      _ ≤ (0.000085345791 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12882 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12882 0.011 Θ) :=
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
    badAllowance 12882 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12882 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12882 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12882 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12882 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12882 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12882 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12882 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12882 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12882 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12882 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035553143510 : ℝ) * 12882 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12882 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003337021987 + 0.003245536482 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12882

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12882
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12882 BstLean.Part154.csC) (piBar (rhoBar 12882 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12882 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12882 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12882 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12882 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12882 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12882 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12882 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12882 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12882 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12882 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12882 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12882 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12882 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12882 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052108232452 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12882) ≤ 0.010522019113 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12882 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035553143510)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010522019113 + 2 * 0.737676 / 12882) := by gcongr
    _ ≤ (0.052108232452 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12882 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12882

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12882
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511682588 : ℝ) ≤ plow 12882 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12882) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052547528641)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360205651) : eMP 12882 0.011 xi bn ≤ 0.001171247927 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12882 : ℝ) * (1 - 0.011))) ≤ 0.000579145192 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001360205651 / (12882 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579145192 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579145192 : ℝ) + 3.141593 * 0.052547528641 / (12882 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001171247927 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052547528641)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360205651) : PiBarMP 12882 12 0.011 xi bn ≤ 0.160096383738 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12882 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036880965972 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.872928552421 : ℝ) ≤ √((12882 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.498898673070 : ℝ) ≤ √(12882 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12882) ≤ 0.122753686826 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036880965972 + 0.052547528641 * 1.772454 / (2 * (112.872928552421 : ℝ))) * (1 + 0.001171247927) +
        8 / (12882 * 113.498898673070) + 0.122753686826 := by gcongr
    _ ≤ (0.160096383738 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052547528641)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360205651) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281340709735) :
    parallelOracle 12882 0.011 xi bn cd ≤ 0.161072485486 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12882 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12882 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511682588 : ℝ) ≤ plow 12882 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.498898673070 : ℝ) ≤ √(12882 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281340709735 : ℝ) / (2 * 0.560511682588 * 113.498898673070)) * 0.160096383738 +
        0.281340709735 ^ 2 / (2 * 0.560511682588 * 113.498898673070) := by gcongr
    _ ≤ (0.161072485486 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052547528641) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360205651)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281340709735) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12882 12882 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511682588 : ℝ) ≤ plow 12882 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.498898673070 : ℝ) ≤ √(12882 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12882 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12882 Θ 1.22 ≤ 0.011683818218 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.498898673070 := by gcongr <;> linarith
      _ ≤ (0.011683818218 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12882 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12882 12882 0.011 ≤ 0.008421993415 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12882 12882 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12882 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12882 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12882 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12882 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161072485486 + 0.011683818218 + (0.008421993415 : ℝ) *
        (1 + 2 * (0.281340709735 + 0.011683818218) / (0.560511682588 * 113.498898673070))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12882]

end BstLean.Part269.N12882

/-! The original eight local profiles supply actual 12882 moment certificates. -/
namespace BstLean.Part269.N12882
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12882 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12882 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12882 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052547528641 ∧
    0 ≤ bN 12882 BstLean.Part154.csC (groupTheta g) ∧ bN 12882 BstLean.Part154.csC (groupTheta g) ≤ 0.001360205651 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12882 12882 0.011
      (momentAllowance 12882 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12882 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12882 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12882 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12882 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12882 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229232477283 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12882 0.011
      (momentAllowance 12882 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12882 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12882
/-! The actual computed-centre upper energy formula at 12882. -/
namespace BstLean.Part269.N12882
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12882

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12882
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12882)
open BstLean.Part268 (cell12882)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084976401446
  | 2 => 0.085910081673
  | 3 => 0.086840639429
  | 4 => 0.087769197950
  | 5 => 0.088697124885
  | 6 => 0.089626069749
  | 7 => 0.090558005103
  | 8 => 0.091495271558
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12882 12882 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12882 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12882

/-! Actual upper energy certificates on all 43 source endpoints at 12882. -/
namespace BstLean.Part269.N12882
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12882)
open BstLean.Part268 (cell12882)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12882 (gMinus 12882) (1 - (cell12882 i).lower) ≤ 1 ∧
    energyUpper 12882 (gMinus 12882) (BstLean.Part211.gPlus 12882)
      (finiteEnergy 12882 12882 0.011) (1 - (cell12882 i).lower) ≤
      (cell12882 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨10,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨11,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨12,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨13,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨14,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨15,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨16,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨17,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨18,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨19,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨20,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨21,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨22,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨23,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨24,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨25,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨26,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨27,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨28,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨29,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨30,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨31,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨32,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨33,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨34,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨35,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨36,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨37,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨38,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨39,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨40,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨41,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨42,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨43,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨44,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨45,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨46,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨47,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨48,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨49,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨50,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨51,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12882) (by norm_num)
        (q := 1 - (cell12882 ⟨52,by decide⟩).lower)
        (by norm_num [cell12882]) (by norm_num [cell12882])
      exact ⟨E.1,E.2.trans (by norm_num [cell12882])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12882

/-! Source-cell containment and simple scalar guards at 12882. -/
namespace BstLean.Part269.N12882
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12882)
open BstLean.Part268 (cell12882)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12882 ⟨10,by decide⟩).lower ∧ (cell12882 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12882 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12882 ⟨11,by decide⟩).lower ∧ (cell12882 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12882 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12882 ⟨12,by decide⟩).lower ∧ (cell12882 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12882 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12882 ⟨13,by decide⟩).lower ∧ (cell12882 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12882 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12882 ⟨14,by decide⟩).lower ∧ (cell12882 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12882 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12882 ⟨15,by decide⟩).lower ∧ (cell12882 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12882 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12882 ⟨16,by decide⟩).lower ∧ (cell12882 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12882 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12882 ⟨17,by decide⟩).lower ∧ (cell12882 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12882 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12882 ⟨18,by decide⟩).lower ∧ (cell12882 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12882 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12882 ⟨19,by decide⟩).lower ∧ (cell12882 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12882 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12882 ⟨20,by decide⟩).lower ∧ (cell12882 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12882 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12882 ⟨21,by decide⟩).lower ∧ (cell12882 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12882 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12882 ⟨22,by decide⟩).lower ∧ (cell12882 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12882 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12882 ⟨23,by decide⟩).lower ∧ (cell12882 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12882 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12882 ⟨24,by decide⟩).lower ∧ (cell12882 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12882 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12882 ⟨25,by decide⟩).lower ∧ (cell12882 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12882 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12882 ⟨26,by decide⟩).lower ∧ (cell12882 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12882 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12882 ⟨27,by decide⟩).lower ∧ (cell12882 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12882 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12882 ⟨28,by decide⟩).lower ∧ (cell12882 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12882 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12882 ⟨29,by decide⟩).lower ∧ (cell12882 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12882 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12882 ⟨30,by decide⟩).lower ∧ (cell12882 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12882 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12882 ⟨31,by decide⟩).lower ∧ (cell12882 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12882 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12882 ⟨32,by decide⟩).lower ∧ (cell12882 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12882 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12882 ⟨33,by decide⟩).lower ∧ (cell12882 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12882 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12882 ⟨34,by decide⟩).lower ∧ (cell12882 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12882 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12882 ⟨35,by decide⟩).lower ∧ (cell12882 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12882 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12882 ⟨36,by decide⟩).lower ∧ (cell12882 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12882 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12882 ⟨37,by decide⟩).lower ∧ (cell12882 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12882 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12882 ⟨38,by decide⟩).lower ∧ (cell12882 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12882 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12882 ⟨39,by decide⟩).lower ∧ (cell12882 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12882 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12882 ⟨40,by decide⟩).lower ∧ (cell12882 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12882 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12882 ⟨41,by decide⟩).lower ∧ (cell12882 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12882 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12882 ⟨42,by decide⟩).lower ∧ (cell12882 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12882 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12882 ⟨43,by decide⟩).lower ∧ (cell12882 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12882 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12882 ⟨44,by decide⟩).lower ∧ (cell12882 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12882 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12882 ⟨45,by decide⟩).lower ∧ (cell12882 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12882 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12882 ⟨46,by decide⟩).lower ∧ (cell12882 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12882 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12882 ⟨47,by decide⟩).lower ∧ (cell12882 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12882 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12882 ⟨48,by decide⟩).lower ∧ (cell12882 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12882 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12882 ⟨49,by decide⟩).lower ∧ (cell12882 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12882 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12882 ⟨50,by decide⟩).lower ∧ (cell12882 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12882 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12882 ⟨51,by decide⟩).lower ∧ (cell12882 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12882 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12882 ⟨52,by decide⟩).lower ∧ (cell12882 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12882 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12882 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12882 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12882,cell12882,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12882 i).lower ∧
    (cell12882 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12882 i).upper ≤ (0.532 : ℝ) ∧
    (cell12882 i).centre ≤ (0.1 : ℝ) ∧ (cell12882 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12882 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12882 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12882

/-! The local source numeric instances at 12882 have no network premises. -/
namespace BstLean.Part269.N12882
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12882)
open BstLean.Part268 (cell12882)

noncomputable def sourceNumerics12882 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12882 (cell12882 i)
      scalarRow12882.M scalarRow12882.H scalarRow12882.xi := by
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
    energy_allowance := scalarRow12882.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12882]
    centre_nonneg := (scalarRow12882.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12882])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12882
/-! Actual 12883 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12883
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12883 ≤ (1.035551751585 : ℝ) := by
  have hr : (113.503303916670 : ℝ) ≤ √(12883 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.503303916670 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12883 12883 (11 / 1000) ≤
    (0.008421666541 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12883) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.503303916670 : ℝ) ≤ √(12883 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12883)
  have hdiv : K / √(12883 : ℝ) ≤ K / 113.503303916670 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.503303916670 ≤ (0.008421666541 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12883.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12883 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12883 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12883 := gPlus_lower 12883
end BstLean.Part269.N12883

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12883
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035551751584 : ℝ) ≤ wn 12883 := by
  have hn : √(12883 : ℝ) ≤ 113.503303916671 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12883 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.503303916671 ≤ 2 / √(12883 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248241240 : ℝ) ≤ rhoBar 12883 BstLean.Part154.csC ∧
    rhoBar 12883 BstLean.Part154.csC ≤ 0.000248241624 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035551751584 : ℝ) / (1.295212 * 12883) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035551751585 : ℝ) / (1.29521 * 12883) := by gcongr
      _ ≤ (0.000248241624 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12883 BstLean.Part154.csC) ≤ 0.000993028120 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12883 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12883 BstLean.Part154.csC) (piBar (rhoBar 12883 BstLean.Part154.csC)) ≤ 0.000189608500 ∧
    cc1 (rhoBar 12883 BstLean.Part154.csC) (piBar (rhoBar 12883 BstLean.Part154.csC)) ≤ 0.000120649173 ∧
    cc2 (rhoBar 12883 BstLean.Part154.csC) ≤ 0.000070037801 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12883 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12883 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12883 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12883 BstLean.Part154.csC * nuR (rhoBar 12883 BstLean.Part154.csC)) ≤ 0.000496498654 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248241624 : ℝ) * 0.000993028120 := by gcongr
      _ ≤ (0.000496498654 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12883 BstLean.Part154.csC) * nuR (rhoBar 12883 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000993028120 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12883 BstLean.Part154.csC) * rhoBar 12883 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248241624 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248241624 / 2 + 0.399 * 0.000993028120 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189608500 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496498654 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120649173 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248241624 / 1.414213562 := by gcongr
      _ ≤ (0.000070037801 : ℝ) := by norm_num

end BstLean.Part269.N12883

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12883
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12883 BstLean.Part154.csC) (piBar (rhoBar 12883 BstLean.Part154.csC)) ≤ 1.55257E-7 := by
  have hr0 : 0 ≤ rhoBar 12883 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12883 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12883 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12883 BstLean.Part154.csC) (piBar (rhoBar 12883 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12883 BstLean.Part154.csC) (piBar (rhoBar 12883 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12883 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189608500 : ℝ) ^ 2 + 0.000120649173 ^ 2 + 3 * 0.000070037801 ^ 2 +
        2 * 0.797885 * 0.000189608500 * 0.000120649173 + 2 * 0.000189608500 * 0.000070037801 +
        4 * 0.797885 * 0.000120649173 * 0.000070037801 := by gcongr
    _ ≤ (1.55257E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12883 BstLean.Part154.csC Θ ≤ 0.002590651873 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12883 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12883 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12883 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12883 BstLean.Part154.csC) (piBar (rhoBar 12883 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12883 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035551751585 * 1.55257E-7 / (0.000248241240 : ℝ) := by gcongr
    _ ≤ 0.002590651873 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12883 BstLean.Part154.csC Θ ≤ 0.002873751248 + 0.000654616000 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12883 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12883 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12883 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035551751585 : ℝ) * ((2 * Θ * 0.000248241624 +
        (6863 / 10000) * 0.000248241624 * 12883 * 0.000993028120) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002873751248 + 0.000654616000 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12883 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12883 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12883 0.011 Θ ∧ gammaRatio 12883 0.011 Θ ≤ 0.000085339051 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12883 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035551751585 : ℝ) * 0.525 / ((1 - 0.011) * 12883) := by gcongr
      _ ≤ (0.000085339051 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12883 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12883 0.011 Θ) :=
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
    badAllowance 12883 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12883 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12883 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12883 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12883 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12883 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12883 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12883 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12883 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12883 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12883 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035551751585 : ℝ) * 12883 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12883 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003336787303 + 0.003245267873 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12883

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12883
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12883 BstLean.Part154.csC) (piBar (rhoBar 12883 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12883 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12883 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12883 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12883 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12883 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12883 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12883 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12883 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12883 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12883 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12883 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12883 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12883 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12883 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052106188270 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12883) ≤ 0.010521610736 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12883 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035551751585)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010521610736 + 2 * 0.737676 / 12883) := by gcongr
    _ ≤ (0.052106188270 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12883 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12883

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12883
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511726538 : ℝ) ≤ plow 12883 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12883) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052547152937)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360092234) : eMP 12883 0.011 xi bn ≤ 0.001171153582 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12883 : ℝ) * (1 - 0.011))) ≤ 0.000579098569 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001360092234 / (12883 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579098569 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579098569 : ℝ) + 3.141593 * 0.052547152937 / (12883 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001171153582 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052547152937)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360092234) : PiBarMP 12883 12 0.011 xi bn ≤ 0.160090056890 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12883 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036879428331 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.877309500182 : ℝ) ≤ √((12883 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.503303916670 : ℝ) ≤ √(12883 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12883) ≤ 0.122748922560 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036879428331 + 0.052547152937 * 1.772454 / (2 * (112.877309500182 : ℝ))) * (1 + 0.001171153582) +
        8 / (12883 * 113.503303916670) + 0.122748922560 := by gcongr
    _ ≤ (0.160090056890 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052547152937)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360092234) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281337846069) :
    parallelOracle 12883 0.011 xi bn cd ≤ 0.161066090422 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12883 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12883 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511726538 : ℝ) ≤ plow 12883 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.503303916670 : ℝ) ≤ √(12883 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281337846069 : ℝ) / (2 * 0.560511726538 * 113.503303916670)) * 0.160090056890 +
        0.281337846069 ^ 2 / (2 * 0.560511726538 * 113.503303916670) := by gcongr
    _ ≤ (0.161066090422 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052547152937) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001360092234)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281337846069) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12883 12883 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511726538 : ℝ) ≤ plow 12883 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.503303916670 : ℝ) ≤ √(12883 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12883 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12883 Θ 1.22 ≤ 0.011683364751 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.503303916670 := by gcongr <;> linarith
      _ ≤ (0.011683364751 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12883 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12883 12883 0.011 ≤ 0.008421666541 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12883 12883 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12883 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12883 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12883 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12883 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161066090422 + 0.011683364751 + (0.008421666541 : ℝ) *
        (1 + 2 * (0.281337846069 + 0.011683364751) / (0.560511726538 * 113.503303916670))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12883]

end BstLean.Part269.N12883

/-! The original eight local profiles supply actual 12883 moment certificates. -/
namespace BstLean.Part269.N12883
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12883 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12883 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12883 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052547152937 ∧
    0 ≤ bN 12883 BstLean.Part154.csC (groupTheta g) ∧ bN 12883 BstLean.Part154.csC (groupTheta g) ≤ 0.001360092234 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12883 12883 0.011
      (momentAllowance 12883 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12883 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12883 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12883 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12883 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12883 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229231657799 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12883 0.011
      (momentAllowance 12883 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12883 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12883
/-! The actual computed-centre upper energy formula at 12883. -/
namespace BstLean.Part269.N12883
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12883

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12883
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12883)
open BstLean.Part268 (cell12883)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084973666039
  | 2 => 0.085907299920
  | 3 => 0.086837805216
  | 4 => 0.087766303710
  | 5 => 0.088694161340
  | 6 => 0.089623025608
  | 7 => 0.090554866730
  | 8 => 0.091492022601
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12883 12883 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12883 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12883

/-! Actual upper energy certificates on all 43 source endpoints at 12883. -/
namespace BstLean.Part269.N12883
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12883)
open BstLean.Part268 (cell12883)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12883 (gMinus 12883) (1 - (cell12883 i).lower) ≤ 1 ∧
    energyUpper 12883 (gMinus 12883) (BstLean.Part211.gPlus 12883)
      (finiteEnergy 12883 12883 0.011) (1 - (cell12883 i).lower) ≤
      (cell12883 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨10,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨11,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨12,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨13,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨14,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨15,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨16,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨17,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨18,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨19,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨20,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨21,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨22,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨23,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨24,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨25,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨26,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨27,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨28,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨29,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨30,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨31,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨32,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨33,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨34,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨35,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨36,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨37,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨38,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨39,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨40,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨41,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨42,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨43,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨44,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨45,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨46,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨47,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨48,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨49,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨50,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨51,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12883) (by norm_num)
        (q := 1 - (cell12883 ⟨52,by decide⟩).lower)
        (by norm_num [cell12883]) (by norm_num [cell12883])
      exact ⟨E.1,E.2.trans (by norm_num [cell12883])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12883

/-! Source-cell containment and simple scalar guards at 12883. -/
namespace BstLean.Part269.N12883
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12883)
open BstLean.Part268 (cell12883)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12883 ⟨10,by decide⟩).lower ∧ (cell12883 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12883 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12883 ⟨11,by decide⟩).lower ∧ (cell12883 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12883 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12883 ⟨12,by decide⟩).lower ∧ (cell12883 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12883 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12883 ⟨13,by decide⟩).lower ∧ (cell12883 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12883 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12883 ⟨14,by decide⟩).lower ∧ (cell12883 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12883 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12883 ⟨15,by decide⟩).lower ∧ (cell12883 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12883 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12883 ⟨16,by decide⟩).lower ∧ (cell12883 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12883 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12883 ⟨17,by decide⟩).lower ∧ (cell12883 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12883 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12883 ⟨18,by decide⟩).lower ∧ (cell12883 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12883 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12883 ⟨19,by decide⟩).lower ∧ (cell12883 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12883 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12883 ⟨20,by decide⟩).lower ∧ (cell12883 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12883 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12883 ⟨21,by decide⟩).lower ∧ (cell12883 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12883 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12883 ⟨22,by decide⟩).lower ∧ (cell12883 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12883 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12883 ⟨23,by decide⟩).lower ∧ (cell12883 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12883 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12883 ⟨24,by decide⟩).lower ∧ (cell12883 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12883 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12883 ⟨25,by decide⟩).lower ∧ (cell12883 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12883 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12883 ⟨26,by decide⟩).lower ∧ (cell12883 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12883 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12883 ⟨27,by decide⟩).lower ∧ (cell12883 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12883 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12883 ⟨28,by decide⟩).lower ∧ (cell12883 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12883 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12883 ⟨29,by decide⟩).lower ∧ (cell12883 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12883 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12883 ⟨30,by decide⟩).lower ∧ (cell12883 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12883 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12883 ⟨31,by decide⟩).lower ∧ (cell12883 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12883 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12883 ⟨32,by decide⟩).lower ∧ (cell12883 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12883 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12883 ⟨33,by decide⟩).lower ∧ (cell12883 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12883 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12883 ⟨34,by decide⟩).lower ∧ (cell12883 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12883 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12883 ⟨35,by decide⟩).lower ∧ (cell12883 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12883 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12883 ⟨36,by decide⟩).lower ∧ (cell12883 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12883 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12883 ⟨37,by decide⟩).lower ∧ (cell12883 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12883 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12883 ⟨38,by decide⟩).lower ∧ (cell12883 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12883 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12883 ⟨39,by decide⟩).lower ∧ (cell12883 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12883 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12883 ⟨40,by decide⟩).lower ∧ (cell12883 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12883 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12883 ⟨41,by decide⟩).lower ∧ (cell12883 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12883 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12883 ⟨42,by decide⟩).lower ∧ (cell12883 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12883 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12883 ⟨43,by decide⟩).lower ∧ (cell12883 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12883 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12883 ⟨44,by decide⟩).lower ∧ (cell12883 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12883 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12883 ⟨45,by decide⟩).lower ∧ (cell12883 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12883 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12883 ⟨46,by decide⟩).lower ∧ (cell12883 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12883 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12883 ⟨47,by decide⟩).lower ∧ (cell12883 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12883 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12883 ⟨48,by decide⟩).lower ∧ (cell12883 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12883 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12883 ⟨49,by decide⟩).lower ∧ (cell12883 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12883 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12883 ⟨50,by decide⟩).lower ∧ (cell12883 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12883 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12883 ⟨51,by decide⟩).lower ∧ (cell12883 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12883 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12883 ⟨52,by decide⟩).lower ∧ (cell12883 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12883 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12883 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12883 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12883,cell12883,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12883 i).lower ∧
    (cell12883 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12883 i).upper ≤ (0.532 : ℝ) ∧
    (cell12883 i).centre ≤ (0.1 : ℝ) ∧ (cell12883 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12883 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12883 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12883

/-! The local source numeric instances at 12883 have no network premises. -/
namespace BstLean.Part269.N12883
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12883)
open BstLean.Part268 (cell12883)

noncomputable def sourceNumerics12883 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12883 (cell12883 i)
      scalarRow12883.M scalarRow12883.H scalarRow12883.xi := by
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
    energy_allowance := scalarRow12883.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12883]
    centre_nonneg := (scalarRow12883.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12883])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12883
/-! Actual 12884 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12884
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12884 ≤ (1.035550359823 : ℝ) := by
  have hr : (113.507708989301 : ℝ) ≤ √(12884 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.507708989301 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12884 12884 (11 / 1000) ≤
    (0.008421339706 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12884) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.507708989301 : ℝ) ≤ √(12884 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12884)
  have hdiv : K / √(12884 : ℝ) ≤ K / 113.507708989301 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.507708989301 ≤ (0.008421339706 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12884.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12884 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12884 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12884 := gPlus_lower 12884
end BstLean.Part269.N12884

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12884
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035550359822 : ℝ) ≤ wn 12884 := by
  have hn : √(12884 : ℝ) ≤ 113.507708989302 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12884 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.507708989302 ≤ 2 / √(12884 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248221639 : ℝ) ≤ rhoBar 12884 BstLean.Part154.csC ∧
    rhoBar 12884 BstLean.Part154.csC ≤ 0.000248222023 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035550359822 : ℝ) / (1.295212 * 12884) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035550359823 : ℝ) / (1.29521 * 12884) := by gcongr
      _ ≤ (0.000248222023 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12884 BstLean.Part154.csC) ≤ 0.000992949707 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12884 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12884 BstLean.Part154.csC) (piBar (rhoBar 12884 BstLean.Part154.csC)) ≤ 0.000189593528 ∧
    cc1 (rhoBar 12884 BstLean.Part154.csC) (piBar (rhoBar 12884 BstLean.Part154.csC)) ≤ 0.000120639647 ∧
    cc2 (rhoBar 12884 BstLean.Part154.csC) ≤ 0.000070032271 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12884 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12884 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12884 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12884 BstLean.Part154.csC * nuR (rhoBar 12884 BstLean.Part154.csC)) ≤ 0.000496459450 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248222023 : ℝ) * 0.000992949707 := by gcongr
      _ ≤ (0.000496459450 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12884 BstLean.Part154.csC) * nuR (rhoBar 12884 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000992949707 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12884 BstLean.Part154.csC) * rhoBar 12884 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248222023 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248222023 / 2 + 0.399 * 0.000992949707 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189593528 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496459450 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120639647 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248222023 / 1.414213562 := by gcongr
      _ ≤ (0.000070032271 : ℝ) := by norm_num

end BstLean.Part269.N12884

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12884
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12884 BstLean.Part154.csC) (piBar (rhoBar 12884 BstLean.Part154.csC)) ≤ 1.55233E-7 := by
  have hr0 : 0 ≤ rhoBar 12884 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12884 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12884 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12884 BstLean.Part154.csC) (piBar (rhoBar 12884 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12884 BstLean.Part154.csC) (piBar (rhoBar 12884 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12884 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189593528 : ℝ) ^ 2 + 0.000120639647 ^ 2 + 3 * 0.000070032271 ^ 2 +
        2 * 0.797885 * 0.000189593528 * 0.000120639647 + 2 * 0.000189593528 * 0.000070032271 +
        4 * 0.797885 * 0.000120639647 * 0.000070032271 := by gcongr
    _ ≤ (1.55233E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12884 BstLean.Part154.csC Θ ≤ 0.002590452463 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12884 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12884 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12884 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12884 BstLean.Part154.csC) (piBar (rhoBar 12884 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12884 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035550359823 * 1.55233E-7 / (0.000248221639 : ℝ) := by gcongr
    _ ≤ 0.002590452463 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12884 BstLean.Part154.csC Θ ≤ 0.002873516603 + 0.000654563433 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12884 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12884 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12884 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035550359823 : ℝ) * ((2 * Θ * 0.000248222023 +
        (6863 / 10000) * 0.000248222023 * 12884 * 0.000992949707) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002873516603 + 0.000654563433 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12884 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12884 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12884 0.011 Θ ∧ gammaRatio 12884 0.011 Θ ≤ 0.000085332313 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12884 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035550359823 : ℝ) * 0.525 / ((1 - 0.011) * 12884) := by gcongr
      _ ≤ (0.000085332313 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12884 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12884 0.011 Θ) :=
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
    badAllowance 12884 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12884 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12884 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12884 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12884 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12884 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12884 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12884 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12884 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12884 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12884 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035550359823 : ℝ) * 12884 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12884 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003336552658 + 0.003245015896 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12884

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12884
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12884 BstLean.Part154.csC) (piBar (rhoBar 12884 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12884 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12884 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12884 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12884 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12884 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12884 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12884 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12884 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12884 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12884 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12884 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12884 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12884 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12884 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052104144335 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12884) ≤ 0.010521202408 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12884 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035550359823)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010521202408 + 2 * 0.737676 / 12884) := by gcongr
    _ ≤ (0.052104144335 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12884 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12884

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12884
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511770482 : ℝ) ≤ plow 12884 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12884) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052546786004)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359987544) : eMP 12884 0.011 xi bn ≤ 0.001171062964 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12884 : ℝ) * (1 - 0.011))) ≤ 0.000579053808 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001359987544 / (12884 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579053808 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579053808 : ℝ) + 3.141593 * 0.052546786004 / (12884 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001171062964 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052546786004)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359987544) : PiBarMP 12884 12 0.011 xi bn ≤ 0.160083849204 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12884 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036878008949 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.881690277918 : ℝ) ≤ √((12884 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.507708989301 : ℝ) ≤ √(12884 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12884) ≤ 0.122744158849 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036878008949 + 0.052546786004 * 1.772454 / (2 * (112.881690277918 : ℝ))) * (1 + 0.001171062964) +
        8 / (12884 * 113.507708989301) + 0.122744158849 := by gcongr
    _ ≤ (0.160083849204 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052546786004)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359987544) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281335001778) :
    parallelOracle 12884 0.011 xi bn cd ≤ 0.161059814900 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12884 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12884 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511770482 : ℝ) ≤ plow 12884 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.507708989301 : ℝ) ≤ √(12884 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281335001778 : ℝ) / (2 * 0.560511770482 * 113.507708989301)) * 0.160083849204 +
        0.281335001778 ^ 2 / (2 * 0.560511770482 * 113.507708989301) := by gcongr
    _ ≤ (0.161059814900 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052546786004) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359987544)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281335001778) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12884 12884 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511770482 : ℝ) ≤ plow 12884 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.507708989301 : ℝ) ≤ √(12884 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12884 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12884 Θ 1.22 ≤ 0.011682911336 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.507708989301 := by gcongr <;> linarith
      _ ≤ (0.011682911336 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12884 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12884 12884 0.011 ≤ 0.008421339706 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12884 12884 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12884 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12884 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12884 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12884 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161059814900 + 0.011682911336 + (0.008421339706 : ℝ) *
        (1 + 2 * (0.281335001778 + 0.011682911336) / (0.560511770482 * 113.507708989301))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12884]

end BstLean.Part269.N12884

/-! The original eight local profiles supply actual 12884 moment certificates. -/
namespace BstLean.Part269.N12884
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12884 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12884 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12884 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052546786004 ∧
    0 ≤ bN 12884 BstLean.Part154.csC (groupTheta g) ∧ bN 12884 BstLean.Part154.csC (groupTheta g) ≤ 0.001359987544 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12884 12884 0.011
      (momentAllowance 12884 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12884 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12884 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12884 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12884 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12884 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229230857443 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12884 0.011
      (momentAllowance 12884 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12884 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12884
/-! The actual computed-centre upper energy formula at 12884. -/
namespace BstLean.Part269.N12884
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12884

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12884
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12884)
open BstLean.Part268 (cell12884)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084970931537
  | 2 => 0.085904519107
  | 3 => 0.086834971986
  | 4 => 0.087763410507
  | 5 => 0.088691198897
  | 6 => 0.089619982648
  | 7 => 0.090551729636
  | 8 => 0.091488775040
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12884 12884 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12884 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12884

/-! Actual upper energy certificates on all 43 source endpoints at 12884. -/
namespace BstLean.Part269.N12884
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12884)
open BstLean.Part268 (cell12884)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12884 (gMinus 12884) (1 - (cell12884 i).lower) ≤ 1 ∧
    energyUpper 12884 (gMinus 12884) (BstLean.Part211.gPlus 12884)
      (finiteEnergy 12884 12884 0.011) (1 - (cell12884 i).lower) ≤
      (cell12884 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨10,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨11,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨12,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨13,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨14,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨15,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨16,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨17,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨18,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨19,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨20,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨21,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨22,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨23,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨24,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨25,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨26,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨27,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨28,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨29,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨30,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨31,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨32,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨33,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨34,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨35,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨36,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨37,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨38,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨39,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨40,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨41,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨42,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨43,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨44,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨45,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨46,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨47,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨48,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨49,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨50,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨51,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12884) (by norm_num)
        (q := 1 - (cell12884 ⟨52,by decide⟩).lower)
        (by norm_num [cell12884]) (by norm_num [cell12884])
      exact ⟨E.1,E.2.trans (by norm_num [cell12884])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12884

/-! Source-cell containment and simple scalar guards at 12884. -/
namespace BstLean.Part269.N12884
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12884)
open BstLean.Part268 (cell12884)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12884 ⟨10,by decide⟩).lower ∧ (cell12884 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12884 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12884 ⟨11,by decide⟩).lower ∧ (cell12884 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12884 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12884 ⟨12,by decide⟩).lower ∧ (cell12884 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12884 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12884 ⟨13,by decide⟩).lower ∧ (cell12884 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12884 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12884 ⟨14,by decide⟩).lower ∧ (cell12884 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12884 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12884 ⟨15,by decide⟩).lower ∧ (cell12884 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12884 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12884 ⟨16,by decide⟩).lower ∧ (cell12884 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12884 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12884 ⟨17,by decide⟩).lower ∧ (cell12884 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12884 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12884 ⟨18,by decide⟩).lower ∧ (cell12884 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12884 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12884 ⟨19,by decide⟩).lower ∧ (cell12884 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12884 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12884 ⟨20,by decide⟩).lower ∧ (cell12884 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12884 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12884 ⟨21,by decide⟩).lower ∧ (cell12884 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12884 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12884 ⟨22,by decide⟩).lower ∧ (cell12884 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12884 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12884 ⟨23,by decide⟩).lower ∧ (cell12884 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12884 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12884 ⟨24,by decide⟩).lower ∧ (cell12884 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12884 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12884 ⟨25,by decide⟩).lower ∧ (cell12884 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12884 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12884 ⟨26,by decide⟩).lower ∧ (cell12884 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12884 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12884 ⟨27,by decide⟩).lower ∧ (cell12884 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12884 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12884 ⟨28,by decide⟩).lower ∧ (cell12884 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12884 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12884 ⟨29,by decide⟩).lower ∧ (cell12884 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12884 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12884 ⟨30,by decide⟩).lower ∧ (cell12884 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12884 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12884 ⟨31,by decide⟩).lower ∧ (cell12884 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12884 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12884 ⟨32,by decide⟩).lower ∧ (cell12884 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12884 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12884 ⟨33,by decide⟩).lower ∧ (cell12884 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12884 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12884 ⟨34,by decide⟩).lower ∧ (cell12884 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12884 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12884 ⟨35,by decide⟩).lower ∧ (cell12884 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12884 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12884 ⟨36,by decide⟩).lower ∧ (cell12884 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12884 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12884 ⟨37,by decide⟩).lower ∧ (cell12884 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12884 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12884 ⟨38,by decide⟩).lower ∧ (cell12884 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12884 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12884 ⟨39,by decide⟩).lower ∧ (cell12884 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12884 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12884 ⟨40,by decide⟩).lower ∧ (cell12884 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12884 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12884 ⟨41,by decide⟩).lower ∧ (cell12884 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12884 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12884 ⟨42,by decide⟩).lower ∧ (cell12884 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12884 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12884 ⟨43,by decide⟩).lower ∧ (cell12884 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12884 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12884 ⟨44,by decide⟩).lower ∧ (cell12884 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12884 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12884 ⟨45,by decide⟩).lower ∧ (cell12884 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12884 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12884 ⟨46,by decide⟩).lower ∧ (cell12884 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12884 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12884 ⟨47,by decide⟩).lower ∧ (cell12884 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12884 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12884 ⟨48,by decide⟩).lower ∧ (cell12884 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12884 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12884 ⟨49,by decide⟩).lower ∧ (cell12884 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12884 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12884 ⟨50,by decide⟩).lower ∧ (cell12884 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12884 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12884 ⟨51,by decide⟩).lower ∧ (cell12884 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12884 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12884 ⟨52,by decide⟩).lower ∧ (cell12884 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12884 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12884 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12884 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12884,cell12884,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12884 i).lower ∧
    (cell12884 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12884 i).upper ≤ (0.532 : ℝ) ∧
    (cell12884 i).centre ≤ (0.1 : ℝ) ∧ (cell12884 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12884 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12884 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12884

/-! The local source numeric instances at 12884 have no network premises. -/
namespace BstLean.Part269.N12884
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12884)
open BstLean.Part268 (cell12884)

noncomputable def sourceNumerics12884 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12884 (cell12884 i)
      scalarRow12884.M scalarRow12884.H scalarRow12884.xi := by
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
    energy_allowance := scalarRow12884.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12884]
    centre_nonneg := (scalarRow12884.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12884])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12884
/-! Actual 12885 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12885
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12885 ≤ (1.035548968224 : ℝ) := by
  have hr : (113.512113890985 : ℝ) ≤ √(12885 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.512113890985 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12885 12885 (11 / 1000) ≤
    (0.008421012909 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12885) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.512113890985 : ℝ) ≤ √(12885 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12885)
  have hdiv : K / √(12885 : ℝ) ≤ K / 113.512113890985 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.512113890985 ≤ (0.008421012909 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12885.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12885 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12885 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12885 := gPlus_lower 12885
end BstLean.Part269.N12885

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12885
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035548968223 : ℝ) ≤ wn 12885 := by
  have hn : √(12885 : ℝ) ≤ 113.512113890986 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12885 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.512113890986 ≤ 2 / √(12885 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248202041 : ℝ) ≤ rhoBar 12885 BstLean.Part154.csC ∧
    rhoBar 12885 BstLean.Part154.csC ≤ 0.000248202425 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035548968223 : ℝ) / (1.295212 * 12885) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035548968224 : ℝ) / (1.29521 * 12885) := by gcongr
      _ ≤ (0.000248202425 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12885 BstLean.Part154.csC) ≤ 0.000992871305 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12885 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12885 BstLean.Part154.csC) (piBar (rhoBar 12885 BstLean.Part154.csC)) ≤ 0.000189578558 ∧
    cc1 (rhoBar 12885 BstLean.Part154.csC) (piBar (rhoBar 12885 BstLean.Part154.csC)) ≤ 0.000120630122 ∧
    cc2 (rhoBar 12885 BstLean.Part154.csC) ≤ 0.000070026742 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12885 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12885 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12885 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12885 BstLean.Part154.csC * nuR (rhoBar 12885 BstLean.Part154.csC)) ≤ 0.000496420252 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248202425 : ℝ) * 0.000992871305 := by gcongr
      _ ≤ (0.000496420252 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12885 BstLean.Part154.csC) * nuR (rhoBar 12885 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000992871305 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12885 BstLean.Part154.csC) * rhoBar 12885 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248202425 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248202425 / 2 + 0.399 * 0.000992871305 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189578558 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496420252 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120630122 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248202425 / 1.414213562 := by gcongr
      _ ≤ (0.000070026742 : ℝ) := by norm_num

end BstLean.Part269.N12885

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12885
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12885 BstLean.Part154.csC) (piBar (rhoBar 12885 BstLean.Part154.csC)) ≤ 1.55208E-7 := by
  have hr0 : 0 ≤ rhoBar 12885 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12885 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12885 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12885 BstLean.Part154.csC) (piBar (rhoBar 12885 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12885 BstLean.Part154.csC) (piBar (rhoBar 12885 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12885 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189578558 : ℝ) ^ 2 + 0.000120630122 ^ 2 + 3 * 0.000070026742 ^ 2 +
        2 * 0.797885 * 0.000189578558 * 0.000120630122 + 2 * 0.000189578558 * 0.000070026742 +
        4 * 0.797885 * 0.000120630122 * 0.000070026742 := by gcongr
    _ ≤ (1.55208E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12885 BstLean.Part154.csC Θ ≤ 0.002590236303 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12885 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12885 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12885 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12885 BstLean.Part154.csC) (piBar (rhoBar 12885 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12885 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035548968224 * 1.55208E-7 / (0.000248202041 : ℝ) := by gcongr
    _ ≤ 0.002590236303 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12885 BstLean.Part154.csC Θ ≤ 0.002873281991 + 0.000654510873 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12885 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12885 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12885 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035548968224 : ℝ) * ((2 * Θ * 0.000248202425 +
        (6863 / 10000) * 0.000248202425 * 12885 * 0.000992871305) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002873281991 + 0.000654510873 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12885 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12885 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12885 0.011 Θ ∧ gammaRatio 12885 0.011 Θ ≤ 0.000085325576 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12885 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035548968224 : ℝ) * 0.525 / ((1 - 0.011) * 12885) := by gcongr
      _ ≤ (0.000085325576 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12885 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12885 0.011 Θ) :=
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
    badAllowance 12885 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12885 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12885 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12885 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12885 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12885 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12885 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12885 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12885 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12885 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12885 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035548968224 : ℝ) * 12885 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12885 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003336318046 + 0.003244747176 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12885

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12885
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12885 BstLean.Part154.csC) (piBar (rhoBar 12885 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12885 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12885 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12885 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12885 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12885 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12885 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12885 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12885 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12885 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12885 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12885 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12885 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12885 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12885 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052102100632 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12885) ≤ 0.010520794126 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12885 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035548968224)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010520794126 + 2 * 0.737676 / 12885) := by gcongr
    _ ≤ (0.052102100632 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12885 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12885

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12885
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511814419 : ℝ) ≤ plow 12885 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12885) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052546410314)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359874060) : eMP 12885 0.011 xi bn ≤ 0.001170968608 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12885 : ℝ) * (1 - 0.011))) ≤ 0.000579007179 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001359874060 / (12885 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000579007179 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000579007179 : ℝ) + 3.141593 * 0.052546410314 / (12885 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001170968608 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052546410314)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359874060) : PiBarMP 12885 12 0.011 xi bn ≤ 0.160077522438 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12885 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036876470276 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.886070885650 : ℝ) ≤ √((12885 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.512113890985 : ℝ) ≤ √(12885 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12885) ≤ 0.122739395693 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036876470276 + 0.052546410314 * 1.772454 / (2 * (112.886070885650 : ℝ))) * (1 + 0.001170968608) +
        8 / (12885 * 113.512113890985) + 0.122739395693 := by gcongr
    _ ≤ (0.160077522438 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052546410314)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359874060) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281332138616) :
    parallelOracle 12885 0.011 xi bn cd ≤ 0.161053419935 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12885 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12885 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511814419 : ℝ) ≤ plow 12885 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.512113890985 : ℝ) ≤ √(12885 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281332138616 : ℝ) / (2 * 0.560511814419 * 113.512113890985)) * 0.160077522438 +
        0.281332138616 ^ 2 / (2 * 0.560511814419 * 113.512113890985) := by gcongr
    _ ≤ (0.161053419935 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052546410314) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359874060)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281332138616) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12885 12885 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511814419 : ℝ) ≤ plow 12885 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.512113890985 : ℝ) ≤ √(12885 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12885 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12885 Θ 1.22 ≤ 0.011682457974 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.512113890985 := by gcongr <;> linarith
      _ ≤ (0.011682457974 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12885 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12885 12885 0.011 ≤ 0.008421012909 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12885 12885 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12885 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12885 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12885 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12885 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161053419935 + 0.011682457974 + (0.008421012909 : ℝ) *
        (1 + 2 * (0.281332138616 + 0.011682457974) / (0.560511814419 * 113.512113890985))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12885]

end BstLean.Part269.N12885

/-! The original eight local profiles supply actual 12885 moment certificates. -/
namespace BstLean.Part269.N12885
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12885 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12885 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12885 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052546410314 ∧
    0 ≤ bN 12885 BstLean.Part154.csC (groupTheta g) ∧ bN 12885 BstLean.Part154.csC (groupTheta g) ≤ 0.001359874060 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12885 12885 0.011
      (momentAllowance 12885 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12885 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12885 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12885 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12885 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12885 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229230037984 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12885 0.011
      (momentAllowance 12885 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12885 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12885
/-! The actual computed-centre upper energy formula at 12885. -/
namespace BstLean.Part269.N12885
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12885

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12885
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12885)
open BstLean.Part268 (cell12885)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084968197938
  | 2 => 0.085901739233
  | 3 => 0.086832139738
  | 4 => 0.087760518340
  | 5 => 0.088688237555
  | 6 => 0.089616940869
  | 7 => 0.090548593819
  | 8 => 0.091485528872
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12885 12885 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12885 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12885

/-! Actual upper energy certificates on all 43 source endpoints at 12885. -/
namespace BstLean.Part269.N12885
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12885)
open BstLean.Part268 (cell12885)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12885 (gMinus 12885) (1 - (cell12885 i).lower) ≤ 1 ∧
    energyUpper 12885 (gMinus 12885) (BstLean.Part211.gPlus 12885)
      (finiteEnergy 12885 12885 0.011) (1 - (cell12885 i).lower) ≤
      (cell12885 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨10,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨11,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨12,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨13,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨14,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨15,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨16,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨17,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨18,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨19,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨20,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨21,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨22,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨23,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨24,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨25,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨26,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨27,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨28,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨29,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨30,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨31,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨32,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨33,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨34,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨35,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨36,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨37,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨38,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨39,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨40,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨41,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨42,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨43,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨44,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨45,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨46,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨47,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨48,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨49,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨50,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨51,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12885) (by norm_num)
        (q := 1 - (cell12885 ⟨52,by decide⟩).lower)
        (by norm_num [cell12885]) (by norm_num [cell12885])
      exact ⟨E.1,E.2.trans (by norm_num [cell12885])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12885

/-! Source-cell containment and simple scalar guards at 12885. -/
namespace BstLean.Part269.N12885
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12885)
open BstLean.Part268 (cell12885)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12885 ⟨10,by decide⟩).lower ∧ (cell12885 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12885 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12885 ⟨11,by decide⟩).lower ∧ (cell12885 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12885 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12885 ⟨12,by decide⟩).lower ∧ (cell12885 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12885 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12885 ⟨13,by decide⟩).lower ∧ (cell12885 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12885 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12885 ⟨14,by decide⟩).lower ∧ (cell12885 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12885 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12885 ⟨15,by decide⟩).lower ∧ (cell12885 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12885 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12885 ⟨16,by decide⟩).lower ∧ (cell12885 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12885 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12885 ⟨17,by decide⟩).lower ∧ (cell12885 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12885 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12885 ⟨18,by decide⟩).lower ∧ (cell12885 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12885 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12885 ⟨19,by decide⟩).lower ∧ (cell12885 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12885 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12885 ⟨20,by decide⟩).lower ∧ (cell12885 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12885 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12885 ⟨21,by decide⟩).lower ∧ (cell12885 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12885 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12885 ⟨22,by decide⟩).lower ∧ (cell12885 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12885 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12885 ⟨23,by decide⟩).lower ∧ (cell12885 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12885 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12885 ⟨24,by decide⟩).lower ∧ (cell12885 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12885 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12885 ⟨25,by decide⟩).lower ∧ (cell12885 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12885 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12885 ⟨26,by decide⟩).lower ∧ (cell12885 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12885 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12885 ⟨27,by decide⟩).lower ∧ (cell12885 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12885 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12885 ⟨28,by decide⟩).lower ∧ (cell12885 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12885 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12885 ⟨29,by decide⟩).lower ∧ (cell12885 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12885 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12885 ⟨30,by decide⟩).lower ∧ (cell12885 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12885 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12885 ⟨31,by decide⟩).lower ∧ (cell12885 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12885 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12885 ⟨32,by decide⟩).lower ∧ (cell12885 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12885 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12885 ⟨33,by decide⟩).lower ∧ (cell12885 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12885 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12885 ⟨34,by decide⟩).lower ∧ (cell12885 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12885 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12885 ⟨35,by decide⟩).lower ∧ (cell12885 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12885 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12885 ⟨36,by decide⟩).lower ∧ (cell12885 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12885 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12885 ⟨37,by decide⟩).lower ∧ (cell12885 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12885 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12885 ⟨38,by decide⟩).lower ∧ (cell12885 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12885 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12885 ⟨39,by decide⟩).lower ∧ (cell12885 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12885 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12885 ⟨40,by decide⟩).lower ∧ (cell12885 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12885 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12885 ⟨41,by decide⟩).lower ∧ (cell12885 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12885 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12885 ⟨42,by decide⟩).lower ∧ (cell12885 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12885 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12885 ⟨43,by decide⟩).lower ∧ (cell12885 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12885 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12885 ⟨44,by decide⟩).lower ∧ (cell12885 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12885 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12885 ⟨45,by decide⟩).lower ∧ (cell12885 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12885 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12885 ⟨46,by decide⟩).lower ∧ (cell12885 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12885 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12885 ⟨47,by decide⟩).lower ∧ (cell12885 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12885 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12885 ⟨48,by decide⟩).lower ∧ (cell12885 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12885 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12885 ⟨49,by decide⟩).lower ∧ (cell12885 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12885 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12885 ⟨50,by decide⟩).lower ∧ (cell12885 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12885 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12885 ⟨51,by decide⟩).lower ∧ (cell12885 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12885 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12885 ⟨52,by decide⟩).lower ∧ (cell12885 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12885 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12885 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12885 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12885,cell12885,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12885 i).lower ∧
    (cell12885 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12885 i).upper ≤ (0.532 : ℝ) ∧
    (cell12885 i).centre ≤ (0.1 : ℝ) ∧ (cell12885 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12885 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12885 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12885

/-! The local source numeric instances at 12885 have no network premises. -/
namespace BstLean.Part269.N12885
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12885)
open BstLean.Part268 (cell12885)

noncomputable def sourceNumerics12885 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12885 (cell12885 i)
      scalarRow12885.M scalarRow12885.H scalarRow12885.xi := by
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
    energy_allowance := scalarRow12885.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12885]
    centre_nonneg := (scalarRow12885.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12885])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12885
/-! Actual 12886 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12886
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12886 ≤ (1.035547576788 : ℝ) := by
  have hr : (113.516518621740 : ℝ) ≤ √(12886 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.516518621740 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12886 12886 (11 / 1000) ≤
    (0.008420686149 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12886) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.516518621740 : ℝ) ≤ √(12886 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12886)
  have hdiv : K / √(12886 : ℝ) ≤ K / 113.516518621740 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.516518621740 ≤ (0.008420686149 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12886.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12886 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12886 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12886 := gPlus_lower 12886
end BstLean.Part269.N12886

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12886
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035547576787 : ℝ) ≤ wn 12886 := by
  have hn : √(12886 : ℝ) ≤ 113.516518621741 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12886 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.516518621741 ≤ 2 / √(12886 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248182446 : ℝ) ≤ rhoBar 12886 BstLean.Part154.csC ∧
    rhoBar 12886 BstLean.Part154.csC ≤ 0.000248182830 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035547576787 : ℝ) / (1.295212 * 12886) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035547576788 : ℝ) / (1.29521 * 12886) := by gcongr
      _ ≤ (0.000248182830 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12886 BstLean.Part154.csC) ≤ 0.000992792915 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12886 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12886 BstLean.Part154.csC) (piBar (rhoBar 12886 BstLean.Part154.csC)) ≤ 0.000189563590 ∧
    cc1 (rhoBar 12886 BstLean.Part154.csC) (piBar (rhoBar 12886 BstLean.Part154.csC)) ≤ 0.000120620598 ∧
    cc2 (rhoBar 12886 BstLean.Part154.csC) ≤ 0.000070021214 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12886 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12886 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12886 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12886 BstLean.Part154.csC * nuR (rhoBar 12886 BstLean.Part154.csC)) ≤ 0.000496381059 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248182830 : ℝ) * 0.000992792915 := by gcongr
      _ ≤ (0.000496381059 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12886 BstLean.Part154.csC) * nuR (rhoBar 12886 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000992792915 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12886 BstLean.Part154.csC) * rhoBar 12886 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248182830 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248182830 / 2 + 0.399 * 0.000992792915 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189563590 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496381059 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120620598 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248182830 / 1.414213562 := by gcongr
      _ ≤ (0.000070021214 : ℝ) := by norm_num

end BstLean.Part269.N12886

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12886
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12886 BstLean.Part154.csC) (piBar (rhoBar 12886 BstLean.Part154.csC)) ≤ 1.55184E-7 := by
  have hr0 : 0 ≤ rhoBar 12886 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12886 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12886 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12886 BstLean.Part154.csC) (piBar (rhoBar 12886 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12886 BstLean.Part154.csC) (piBar (rhoBar 12886 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12886 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189563590 : ℝ) ^ 2 + 0.000120620598 ^ 2 + 3 * 0.000070021214 ^ 2 +
        2 * 0.797885 * 0.000189563590 * 0.000120620598 + 2 * 0.000189563590 * 0.000070021214 +
        4 * 0.797885 * 0.000120620598 * 0.000070021214 := by gcongr
    _ ≤ (1.55184E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12886 BstLean.Part154.csC Θ ≤ 0.002590036770 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12886 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12886 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12886 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12886 BstLean.Part154.csC) (piBar (rhoBar 12886 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12886 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035547576788 * 1.55184E-7 / (0.000248182446 : ℝ) := by gcongr
    _ ≤ 0.002590036770 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12886 BstLean.Part154.csC Θ ≤ 0.002873047415 + 0.000654458322 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12886 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12886 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12886 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035547576788 : ℝ) * ((2 * Θ * 0.000248182830 +
        (6863 / 10000) * 0.000248182830 * 12886 * 0.000992792915) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002873047415 + 0.000654458322 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12886 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12886 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12886 0.011 Θ ∧ gammaRatio 12886 0.011 Θ ≤ 0.000085318840 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12886 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035547576788 : ℝ) * 0.525 / ((1 - 0.011) * 12886) := by gcongr
      _ ≤ (0.000085318840 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12886 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12886 0.011 Θ) :=
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
    badAllowance 12886 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12886 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12886 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12886 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12886 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12886 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12886 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12886 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12886 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12886 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12886 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035547576788 : ℝ) * 12886 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12886 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003336083470 + 0.003244495092 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12886

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12886
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12886 BstLean.Part154.csC) (piBar (rhoBar 12886 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12886 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12886 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12886 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12886 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12886 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12886 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12886 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12886 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12886 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12886 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12886 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12886 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12886 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12886 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052100057176 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12886) ≤ 0.010520385893 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12886 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035547576788)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010520385893 + 2 * 0.737676 / 12886) := by gcongr
    _ ≤ (0.052100057176 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12886 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12886

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12886
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511858350 : ℝ) ≤ plow 12886 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12886) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052546043394)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359769305) : eMP 12886 0.011 xi bn ≤ 0.001170877976 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12886 : ℝ) * (1 - 0.011))) ≤ 0.000578962411 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001359769305 / (12886 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578962411 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578962411 : ℝ) + 3.141593 * 0.052546043394 / (12886 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001170877976 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052546043394)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359769305) : PiBarMP 12886 12 0.011 xi bn ≤ 0.160071314870 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12886 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036875049899 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.890451323395 : ℝ) ≤ √((12886 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.516518621740 : ℝ) ≤ √(12886 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12886) ≤ 0.122734633091 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036875049899 + 0.052546043394 * 1.772454 / (2 * (112.890451323395 : ℝ))) * (1 + 0.001170877976) +
        8 / (12886 * 113.516518621740) + 0.122734633091 := by gcongr
    _ ≤ (0.160071314870 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052546043394)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359769305) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281329294827) :
    parallelOracle 12886 0.011 xi bn cd ≤ 0.161047144548 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12886 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12886 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511858350 : ℝ) ≤ plow 12886 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.516518621740 : ℝ) ≤ √(12886 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281329294827 : ℝ) / (2 * 0.560511858350 * 113.516518621740)) * 0.160071314870 +
        0.281329294827 ^ 2 / (2 * 0.560511858350 * 113.516518621740) := by gcongr
    _ ≤ (0.161047144548 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052546043394) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359769305)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281329294827) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12886 12886 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511858350 : ℝ) ≤ plow 12886 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.516518621740 : ℝ) ≤ √(12886 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12886 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12886 Θ 1.22 ≤ 0.011682004665 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.516518621740 := by gcongr <;> linarith
      _ ≤ (0.011682004665 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12886 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12886 12886 0.011 ≤ 0.008420686149 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12886 12886 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12886 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12886 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12886 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12886 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161047144548 + 0.011682004665 + (0.008420686149 : ℝ) *
        (1 + 2 * (0.281329294827 + 0.011682004665) / (0.560511858350 * 113.516518621740))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12886]

end BstLean.Part269.N12886

/-! The original eight local profiles supply actual 12886 moment certificates. -/
namespace BstLean.Part269.N12886
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12886 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12886 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12886 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052546043394 ∧
    0 ≤ bN 12886 BstLean.Part154.csC (groupTheta g) ∧ bN 12886 BstLean.Part154.csC (groupTheta g) ≤ 0.001359769305 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12886 12886 0.011
      (momentAllowance 12886 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12886 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12886 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12886 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12886 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12886 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229229237651 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12886 0.011
      (momentAllowance 12886 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12886 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12886
/-! The actual computed-centre upper energy formula at 12886. -/
namespace BstLean.Part269.N12886
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12886

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12886
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12886)
open BstLean.Part268 (cell12886)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084965465243
  | 2 => 0.085898960298
  | 3 => 0.086829308472
  | 4 => 0.087757627208
  | 5 => 0.088685277313
  | 6 => 0.089613900270
  | 7 => 0.090545459277
  | 8 => 0.091482284096
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12886 12886 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12886 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12886

/-! Actual upper energy certificates on all 43 source endpoints at 12886. -/
namespace BstLean.Part269.N12886
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12886)
open BstLean.Part268 (cell12886)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12886 (gMinus 12886) (1 - (cell12886 i).lower) ≤ 1 ∧
    energyUpper 12886 (gMinus 12886) (BstLean.Part211.gPlus 12886)
      (finiteEnergy 12886 12886 0.011) (1 - (cell12886 i).lower) ≤
      (cell12886 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨10,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨11,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨12,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨13,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨14,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨15,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨16,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨17,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨18,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨19,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨20,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨21,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨22,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨23,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨24,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨25,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨26,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨27,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨28,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨29,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨30,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨31,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨32,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨33,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨34,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨35,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨36,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨37,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨38,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨39,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨40,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨41,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨42,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨43,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨44,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨45,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨46,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨47,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨48,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨49,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨50,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨51,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12886) (by norm_num)
        (q := 1 - (cell12886 ⟨52,by decide⟩).lower)
        (by norm_num [cell12886]) (by norm_num [cell12886])
      exact ⟨E.1,E.2.trans (by norm_num [cell12886])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12886

/-! Source-cell containment and simple scalar guards at 12886. -/
namespace BstLean.Part269.N12886
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12886)
open BstLean.Part268 (cell12886)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12886 ⟨10,by decide⟩).lower ∧ (cell12886 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12886 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12886 ⟨11,by decide⟩).lower ∧ (cell12886 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12886 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12886 ⟨12,by decide⟩).lower ∧ (cell12886 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12886 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12886 ⟨13,by decide⟩).lower ∧ (cell12886 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12886 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12886 ⟨14,by decide⟩).lower ∧ (cell12886 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12886 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12886 ⟨15,by decide⟩).lower ∧ (cell12886 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12886 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12886 ⟨16,by decide⟩).lower ∧ (cell12886 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12886 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12886 ⟨17,by decide⟩).lower ∧ (cell12886 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12886 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12886 ⟨18,by decide⟩).lower ∧ (cell12886 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12886 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12886 ⟨19,by decide⟩).lower ∧ (cell12886 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12886 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12886 ⟨20,by decide⟩).lower ∧ (cell12886 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12886 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12886 ⟨21,by decide⟩).lower ∧ (cell12886 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12886 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12886 ⟨22,by decide⟩).lower ∧ (cell12886 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12886 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12886 ⟨23,by decide⟩).lower ∧ (cell12886 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12886 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12886 ⟨24,by decide⟩).lower ∧ (cell12886 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12886 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12886 ⟨25,by decide⟩).lower ∧ (cell12886 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12886 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12886 ⟨26,by decide⟩).lower ∧ (cell12886 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12886 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12886 ⟨27,by decide⟩).lower ∧ (cell12886 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12886 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12886 ⟨28,by decide⟩).lower ∧ (cell12886 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12886 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12886 ⟨29,by decide⟩).lower ∧ (cell12886 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12886 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12886 ⟨30,by decide⟩).lower ∧ (cell12886 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12886 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12886 ⟨31,by decide⟩).lower ∧ (cell12886 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12886 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12886 ⟨32,by decide⟩).lower ∧ (cell12886 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12886 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12886 ⟨33,by decide⟩).lower ∧ (cell12886 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12886 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12886 ⟨34,by decide⟩).lower ∧ (cell12886 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12886 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12886 ⟨35,by decide⟩).lower ∧ (cell12886 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12886 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12886 ⟨36,by decide⟩).lower ∧ (cell12886 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12886 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12886 ⟨37,by decide⟩).lower ∧ (cell12886 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12886 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12886 ⟨38,by decide⟩).lower ∧ (cell12886 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12886 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12886 ⟨39,by decide⟩).lower ∧ (cell12886 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12886 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12886 ⟨40,by decide⟩).lower ∧ (cell12886 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12886 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12886 ⟨41,by decide⟩).lower ∧ (cell12886 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12886 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12886 ⟨42,by decide⟩).lower ∧ (cell12886 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12886 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12886 ⟨43,by decide⟩).lower ∧ (cell12886 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12886 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12886 ⟨44,by decide⟩).lower ∧ (cell12886 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12886 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12886 ⟨45,by decide⟩).lower ∧ (cell12886 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12886 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12886 ⟨46,by decide⟩).lower ∧ (cell12886 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12886 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12886 ⟨47,by decide⟩).lower ∧ (cell12886 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12886 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12886 ⟨48,by decide⟩).lower ∧ (cell12886 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12886 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12886 ⟨49,by decide⟩).lower ∧ (cell12886 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12886 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12886 ⟨50,by decide⟩).lower ∧ (cell12886 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12886 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12886 ⟨51,by decide⟩).lower ∧ (cell12886 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12886 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12886 ⟨52,by decide⟩).lower ∧ (cell12886 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12886 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12886 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12886 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12886,cell12886,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12886 i).lower ∧
    (cell12886 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12886 i).upper ≤ (0.532 : ℝ) ∧
    (cell12886 i).centre ≤ (0.1 : ℝ) ∧ (cell12886 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12886 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12886 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12886

/-! The local source numeric instances at 12886 have no network premises. -/
namespace BstLean.Part269.N12886
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12886)
open BstLean.Part268 (cell12886)

noncomputable def sourceNumerics12886 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12886 (cell12886 i)
      scalarRow12886.M scalarRow12886.H scalarRow12886.xi := by
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
    energy_allowance := scalarRow12886.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12886]
    centre_nonneg := (scalarRow12886.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12886])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12886
/-! Actual 12887 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12887
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12887 ≤ (1.035546185515 : ℝ) := by
  have hr : (113.520923181587 : ℝ) ≤ √(12887 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (113.520923181587 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12887 12887 (11 / 1000) ≤
    (0.008420359428 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12887) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (113.520923181587 : ℝ) ≤ √(12887 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12887)
  have hdiv : K / √(12887 : ℝ) ≤ K / 113.520923181587 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 113.520923181587 ≤ (0.008420359428 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12887.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12887 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12887 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12887 := gPlus_lower 12887
end BstLean.Part269.N12887

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12887
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035546185514 : ℝ) ≤ wn 12887 := by
  have hn : √(12887 : ℝ) ≤ 113.520923181588 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12887 : ℝ) := by positivity
  have hd : (2 : ℝ) / 113.520923181588 ≤ 2 / √(12887 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000248162854 : ℝ) ≤ rhoBar 12887 BstLean.Part154.csC ∧
    rhoBar 12887 BstLean.Part154.csC ≤ 0.000248163239 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035546185514 : ℝ) / (1.295212 * 12887) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035546185515 : ℝ) / (1.29521 * 12887) := by gcongr
      _ ≤ (0.000248163239 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12887 BstLean.Part154.csC) ≤ 0.000992714541 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12887 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12887 BstLean.Part154.csC) (piBar (rhoBar 12887 BstLean.Part154.csC)) ≤ 0.000189548626 ∧
    cc1 (rhoBar 12887 BstLean.Part154.csC) (piBar (rhoBar 12887 BstLean.Part154.csC)) ≤ 0.000120611076 ∧
    cc2 (rhoBar 12887 BstLean.Part154.csC) ≤ 0.000070015686 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12887 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12887 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12887 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12887 BstLean.Part154.csC * nuR (rhoBar 12887 BstLean.Part154.csC)) ≤ 0.000496341875 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000248163239 : ℝ) * 0.000992714541 := by gcongr
      _ ≤ (0.000496341875 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12887 BstLean.Part154.csC) * nuR (rhoBar 12887 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000992714541 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12887 BstLean.Part154.csC) * rhoBar 12887 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000248163239 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000248163239 / 2 + 0.399 * 0.000992714541 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000189548626 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000496341875 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000120611076 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000248163239 / 1.414213562 := by gcongr
      _ ≤ (0.000070015686 : ℝ) := by norm_num

end BstLean.Part269.N12887

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12887
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12887 BstLean.Part154.csC) (piBar (rhoBar 12887 BstLean.Part154.csC)) ≤ 1.55159E-7 := by
  have hr0 : 0 ≤ rhoBar 12887 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12887 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12887 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12887 BstLean.Part154.csC) (piBar (rhoBar 12887 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12887 BstLean.Part154.csC) (piBar (rhoBar 12887 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12887 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000189548626 : ℝ) ^ 2 + 0.000120611076 ^ 2 + 3 * 0.000070015686 ^ 2 +
        2 * 0.797885 * 0.000189548626 * 0.000120611076 + 2 * 0.000189548626 * 0.000070015686 +
        4 * 0.797885 * 0.000120611076 * 0.000070015686 := by gcongr
    _ ≤ (1.55159E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12887 BstLean.Part154.csC Θ ≤ 0.002589820483 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12887 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12887 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12887 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12887 BstLean.Part154.csC) (piBar (rhoBar 12887 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12887 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035546185515 * 1.55159E-7 / (0.000248162854 : ℝ) := by gcongr
    _ ≤ 0.002589820483 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12887 BstLean.Part154.csC Θ ≤ 0.002872812898 + 0.000654405781 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12887 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12887 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12887 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035546185515 : ℝ) * ((2 * Θ * 0.000248163239 +
        (6863 / 10000) * 0.000248163239 * 12887 * 0.000992714541) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002872812898 + 0.000654405781 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12887 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12887 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12887 0.011 Θ ∧ gammaRatio 12887 0.011 Θ ≤ 0.000085312104 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12887 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035546185515 : ℝ) * 0.525 / ((1 - 0.011) * 12887) := by gcongr
      _ ≤ (0.000085312104 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12887 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12887 0.011 Θ) :=
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
    badAllowance 12887 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000463036055 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12887 BstLean.Part154.csC) 1.22 ≤ 1.6832E-8 := by
    have he : (17.9 : ℝ) ≤ gap 2 (rhoBar 12887 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12887 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12887 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12887 0.011 Θ) 1.12 ≤ 2.0559E-8 := by
    have he : (17.7 : ℝ) ≤ gap 1 (gammaRatio 12887 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12887 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12887 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_7_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12887 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12887 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035546185515 : ℝ) * 12887 *
        (1.6832E-8 / 1.1045361 + 2.0559E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000463036055 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12887 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003335848953 + 0.003244226264 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12887

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12887
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12887 BstLean.Part154.csC) (piBar (rhoBar 12887 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12887 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12887 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12887 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12887 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12887 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12887 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12887 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12887 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12887 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12887 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12887 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12887 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12887 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12887 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052098013956 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12887) ≤ 0.010519977707 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12887 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035546185515)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010519977707 + 2 * 0.737676 / 12887) := by gcongr
    _ ≤ (0.052098013956 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12887 12 ≤ 0.0015 := by
  exact BstLean.Part269.S21.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12887

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12887
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560511902273 : ℝ) ≤ plow 12887 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12887) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052545667742)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359655754) : eMP 12887 0.011 xi bn ≤ 0.001170783605 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12887 : ℝ) * (1 - 0.011))) ≤ 0.000578915774 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001359655754 / (12887 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000578915774 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000578915774 : ℝ) + 3.141593 * 0.052545667742 / (12887 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001170783605 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052545667742)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359655754) : PiBarMP 12887 12 0.011 xi bn ≤ 0.160064988183 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12887 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036873510194 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.894831591176 : ℝ) ≤ √((12887 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (113.520923181587 : ℝ) ≤ √(12887 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12887) ≤ 0.122729871043 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036873510194 + 0.052545667742 * 1.772454 / (2 * (112.894831591176 : ℝ))) * (1 + 0.001170783605) +
        8 / (12887 * 113.520923181587) + 0.122729871043 := by gcongr
    _ ≤ (0.160064988183 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052545667742)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359655754) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281326432225) :
    parallelOracle 12887 0.011 xi bn cd ≤ 0.161040749680 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12887 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12887 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560511902273 : ℝ) ≤ plow 12887 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.520923181587 : ℝ) ≤ √(12887 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281326432225 : ℝ) / (2 * 0.560511902273 * 113.520923181587)) * 0.160064988183 +
        0.281326432225 ^ 2 / (2 * 0.560511902273 * 113.520923181587) := by gcongr
    _ ≤ (0.161040749680 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052545667742) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001359655754)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281326432225) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12887 12887 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560511902273 : ℝ) ≤ plow 12887 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (113.520923181587 : ℝ) ≤ √(12887 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12887 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12887 Θ 1.22 ≤ 0.011681551408 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 113.520923181587 := by gcongr <;> linarith
      _ ≤ (0.011681551408 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12887 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12887 12887 0.011 ≤ 0.008420359428 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12887 12887 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12887 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12887 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12887 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12887 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.161040749680 + 0.011681551408 + (0.008420359428 : ℝ) *
        (1 + 2 * (0.281326432225 + 0.011681551408) / (0.560511902273 * 113.520923181587))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12887]

end BstLean.Part269.N12887

/-! The original eight local profiles supply actual 12887 moment certificates. -/
namespace BstLean.Part269.N12887
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12887 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12887 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12887 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052545667742 ∧
    0 ≤ bN 12887 BstLean.Part154.csC (groupTheta g) ∧ bN 12887 BstLean.Part154.csC (groupTheta g) ≤ 0.001359655754 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12887 12887 0.011
      (momentAllowance 12887 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12887 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12887 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12887 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12887 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12887 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229228418269 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12887 0.011
      (momentAllowance 12887 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12887 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12887
/-! The actual computed-centre upper energy formula at 12887. -/
namespace BstLean.Part269.N12887
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12887

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12887
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12887)
open BstLean.Part268 (cell12887)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084962733450
  | 2 => 0.085896182299
  | 3 => 0.086826478186
  | 4 => 0.087754737109
  | 5 => 0.088682318170
  | 6 => 0.089610860849
  | 7 => 0.090542326010
  | 8 => 0.091479040711
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12887 12887 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12887 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N12887

/-! Actual upper energy certificates on all 43 source endpoints at 12887. -/
namespace BstLean.Part269.N12887
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12887)
open BstLean.Part268 (cell12887)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12887 (gMinus 12887) (1 - (cell12887 i).lower) ≤ 1 ∧
    energyUpper 12887 (gMinus 12887) (BstLean.Part211.gPlus 12887)
      (finiteEnergy 12887 12887 0.011) (1 - (cell12887 i).lower) ≤
      (cell12887 i).energy := by
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
      have E := BstLean.Part269.S21.uniformEnergy10 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨10,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy11 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨11,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy12 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨12,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy13 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨13,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy14 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨14,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy15 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨15,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy16 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨16,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy17 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨17,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy18 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨18,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy19 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨19,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy20 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨20,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy21 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨21,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy22 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨22,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy23 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨23,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy24 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨24,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy25 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨25,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy26 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨26,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy27 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨27,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy28 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨28,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy29 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨29,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy30 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨30,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy31 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨31,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy32 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨32,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy33 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨33,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy34 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨34,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy35 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨35,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy36 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨36,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy37 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨37,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy38 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨38,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy39 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨39,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy40 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨40,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy41 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨41,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy42 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨42,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy43 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨43,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy44 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨44,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy45 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨45,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy46 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨46,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy47 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨47,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy48 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨48,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy49 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨49,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy50 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨50,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy51 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨51,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S21.uniformEnergy52 (n := 12887) (by norm_num)
        (q := 1 - (cell12887 ⟨52,by decide⟩).lower)
        (by norm_num [cell12887]) (by norm_num [cell12887])
      exact ⟨E.1,E.2.trans (by norm_num [cell12887])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12887

/-! Source-cell containment and simple scalar guards at 12887. -/
namespace BstLean.Part269.N12887
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12887)
open BstLean.Part268 (cell12887)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12887 ⟨10,by decide⟩).lower ∧ (cell12887 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12887 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12887 ⟨11,by decide⟩).lower ∧ (cell12887 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12887 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12887 ⟨12,by decide⟩).lower ∧ (cell12887 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12887 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12887 ⟨13,by decide⟩).lower ∧ (cell12887 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12887 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12887 ⟨14,by decide⟩).lower ∧ (cell12887 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12887 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12887 ⟨15,by decide⟩).lower ∧ (cell12887 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12887 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12887 ⟨16,by decide⟩).lower ∧ (cell12887 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12887 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12887 ⟨17,by decide⟩).lower ∧ (cell12887 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12887 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12887 ⟨18,by decide⟩).lower ∧ (cell12887 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12887 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12887 ⟨19,by decide⟩).lower ∧ (cell12887 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12887 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12887 ⟨20,by decide⟩).lower ∧ (cell12887 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12887 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12887 ⟨21,by decide⟩).lower ∧ (cell12887 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12887 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12887 ⟨22,by decide⟩).lower ∧ (cell12887 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12887 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12887 ⟨23,by decide⟩).lower ∧ (cell12887 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12887 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12887 ⟨24,by decide⟩).lower ∧ (cell12887 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12887 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12887 ⟨25,by decide⟩).lower ∧ (cell12887 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12887 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12887 ⟨26,by decide⟩).lower ∧ (cell12887 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12887 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12887 ⟨27,by decide⟩).lower ∧ (cell12887 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12887 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12887 ⟨28,by decide⟩).lower ∧ (cell12887 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12887 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12887 ⟨29,by decide⟩).lower ∧ (cell12887 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12887 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12887 ⟨30,by decide⟩).lower ∧ (cell12887 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12887 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12887 ⟨31,by decide⟩).lower ∧ (cell12887 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12887 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12887 ⟨32,by decide⟩).lower ∧ (cell12887 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12887 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12887 ⟨33,by decide⟩).lower ∧ (cell12887 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12887 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12887 ⟨34,by decide⟩).lower ∧ (cell12887 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12887 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12887 ⟨35,by decide⟩).lower ∧ (cell12887 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12887 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12887 ⟨36,by decide⟩).lower ∧ (cell12887 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12887 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12887 ⟨37,by decide⟩).lower ∧ (cell12887 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12887 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12887 ⟨38,by decide⟩).lower ∧ (cell12887 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12887 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12887 ⟨39,by decide⟩).lower ∧ (cell12887 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12887 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12887 ⟨40,by decide⟩).lower ∧ (cell12887 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12887 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12887 ⟨41,by decide⟩).lower ∧ (cell12887 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12887 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12887 ⟨42,by decide⟩).lower ∧ (cell12887 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12887 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12887 ⟨43,by decide⟩).lower ∧ (cell12887 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12887 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12887 ⟨44,by decide⟩).lower ∧ (cell12887 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12887 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12887 ⟨45,by decide⟩).lower ∧ (cell12887 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12887 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12887 ⟨46,by decide⟩).lower ∧ (cell12887 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12887 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12887 ⟨47,by decide⟩).lower ∧ (cell12887 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12887 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12887 ⟨48,by decide⟩).lower ∧ (cell12887 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12887 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12887 ⟨49,by decide⟩).lower ∧ (cell12887 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12887 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12887 ⟨50,by decide⟩).lower ∧ (cell12887 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12887 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12887 ⟨51,by decide⟩).lower ∧ (cell12887 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12887 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12887 ⟨52,by decide⟩).lower ∧ (cell12887 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12887 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12887 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12887 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12887,cell12887,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12887 i).lower ∧
    (cell12887 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12887 i).upper ≤ (0.532 : ℝ) ∧
    (cell12887 i).centre ≤ (0.1 : ℝ) ∧ (cell12887 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12887 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12887 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12887

/-! The local source numeric instances at 12887 have no network premises. -/
namespace BstLean.Part269.N12887
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12887)
open BstLean.Part268 (cell12887)

noncomputable def sourceNumerics12887 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12887 (cell12887 i)
      scalarRow12887.M scalarRow12887.H scalarRow12887.xi := by
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
    energy_allowance := scalarRow12887.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12887]
    centre_nonneg := (scalarRow12887.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D21.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12887])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12887