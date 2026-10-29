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
import BstLean.Part269Direction33
import BstLean.Part269Shared33
import BstLean.Part269Finite
import BstLean.Part269Rows33
import BstLean.Part269Source
/-! Actual 13188 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13188
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13188 ≤ (1.035134673267 : ℝ) := by
  have hr : (114.839017759644 : ℝ) ≤ √(13188 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.839017759644 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13188 13188 (11 / 1000) ≤
    (0.008323711851 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13188) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.839017759644 : ℝ) ≤ √(13188 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13188)
  have hdiv : K / √(13188 : ℝ) ≤ K / 114.839017759644 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.839017759644 ≤ (0.008323711851 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13188.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13188 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13188 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13188 := gPlus_lower 13188
end BstLean.Part269.N13188

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13188
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035134673266 : ℝ) ≤ wn 13188 := by
  have hn : √(13188 : ℝ) ≤ 114.839017759645 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13188 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.839017759645 ≤ 2 / √(13188 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242402474 : ℝ) ≤ rhoBar 13188 BstLean.Part154.csC ∧
    rhoBar 13188 BstLean.Part154.csC ≤ 0.000242402850 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035134673266 : ℝ) / (1.295212 * 13188) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035134673267 : ℝ) / (1.29521 * 13188) := by gcongr
      _ ≤ (0.000242402850 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13188 BstLean.Part154.csC) ≤ 0.000969670160 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13188 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13188 BstLean.Part154.csC) (piBar (rhoBar 13188 BstLean.Part154.csC)) ≤ 0.000185148608 ∧
    cc1 (rhoBar 13188 BstLean.Part154.csC) (piBar (rhoBar 13188 BstLean.Part154.csC)) ≤ 0.000117811355 ∧
    cc2 (rhoBar 13188 BstLean.Part154.csC) ≤ 0.000068390475 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13188 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13188 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13188 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13188 BstLean.Part154.csC * nuR (rhoBar 13188 BstLean.Part154.csC)) ≤ 0.000484820390 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242402850 : ℝ) * 0.000969670160 := by gcongr
      _ ≤ (0.000484820390 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13188 BstLean.Part154.csC) * nuR (rhoBar 13188 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000969670160 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13188 BstLean.Part154.csC) * rhoBar 13188 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242402850 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242402850 / 2 + 0.399 * 0.000969670160 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185148608 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484820390 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117811355 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242402850 / 1.414213562 := by gcongr
      _ ≤ (0.000068390475 : ℝ) := by norm_num

end BstLean.Part269.N13188

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13188
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13188 BstLean.Part154.csC) (piBar (rhoBar 13188 BstLean.Part154.csC)) ≤ 1.48039E-7 := by
  have hr0 : 0 ≤ rhoBar 13188 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13188 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13188 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13188 BstLean.Part154.csC) (piBar (rhoBar 13188 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13188 BstLean.Part154.csC) (piBar (rhoBar 13188 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13188 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185148608 : ℝ) ^ 2 + 0.000117811355 ^ 2 + 3 * 0.000068390475 ^ 2 +
        2 * 0.797885 * 0.000185148608 * 0.000117811355 + 2 * 0.000185148608 * 0.000068390475 +
        4 * 0.797885 * 0.000117811355 * 0.000068390475 := by gcongr
    _ ≤ (1.48039E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13188 BstLean.Part154.csC Θ ≤ 0.002528692045 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13188 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13188 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13188 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13188 BstLean.Part154.csC) (piBar (rhoBar 13188 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13188 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035134673267 * 1.48039E-7 / (0.000242402474 : ℝ) := by gcongr
    _ ≤ 0.002528692045 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13188 BstLean.Part154.csC Θ ≤ 0.002803895059 + 0.000638961635 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13188 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13188 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13188 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035134673267 : ℝ) * ((2 * Θ * 0.000242402850 +
        (6863 / 10000) * 0.000242402850 * 13188 * 0.000969670160) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002803895059 + 0.000638961635 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13188 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13188 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13188 0.011 Θ ∧ gammaRatio 13188 0.011 Θ ≤ 0.000083331832 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13188 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035134673267 : ℝ) * 0.525 / ((1 - 0.011) * 13188) := by gcongr
      _ ≤ (0.000083331832 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13188 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13188 0.011 Θ) :=
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
    badAllowance 13188 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13188 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13188 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13188 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13188 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13188 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13188 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13188 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13188 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13188 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13188 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035134673267 : ℝ) * 13188 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13188 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003121371259 + 0.003167653680 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13188

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13188
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13188 BstLean.Part154.csC) (piBar (rhoBar 13188 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13188 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13188 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13188 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13188 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13188 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13188 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13188 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13188 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13188 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13188 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13188 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13188 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13188 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13188 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051493682046 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13188) ≤ 0.010399231937 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13188 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035134673267)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010399231937 + 2 * 0.737676 / 13188) := by gcongr
    _ ≤ (0.051493682046 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13188 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13188

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13188
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524820480 : ℝ) ≤ plow 13188 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13188) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052290989441)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327563324) : eMP 13188 0.011 xi bn ≤ 0.001143549158 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13188 : ℝ) * (1 - 0.011))) ≤ 0.000565477030 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001327563324 / (13188 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565477030 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565477030 : ℝ) + 3.141593 * 0.052290989441 / (13188 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001143549158 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052290989441)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327563324) : PiBarMP 13188 12 0.011 xi bn ≤ 0.158210135923 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13188 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036435742397 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.205656602464 : ℝ) ≤ √((13188 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.839017759644 : ℝ) ≤ √(13188 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13188) ≤ 0.121321207153 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036435742397 + 0.052290989441 * 1.772454 / (2 * (114.205656602464 : ℝ))) * (1 + 0.001143549158) +
        8 / (13188 * 114.839017759644) + 0.121321207153 := by gcongr
    _ ≤ (0.158210135923 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052290989441)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327563324) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280165913507) :
    parallelOracle 13188 0.011 xi bn cd ≤ 0.159164134663 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13188 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13188 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524820480 : ℝ) ≤ plow 13188 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.839017759644 : ℝ) ≤ √(13188 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280165913507 : ℝ) / (2 * 0.560524820480 * 114.839017759644)) * 0.158210135923 +
        0.280165913507 ^ 2 / (2 * 0.560524820480 * 114.839017759644) := by gcongr
    _ ≤ (0.159164134663 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052290989441) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327563324)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280165913507) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13188 13188 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524820480 : ℝ) ≤ plow 13188 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.839017759644 : ℝ) ≤ √(13188 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13188 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13188 Θ 1.22 ≤ 0.011547473376 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.839017759644 := by gcongr <;> linarith
      _ ≤ (0.011547473376 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13188 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13188 13188 0.011 ≤ 0.008323711851 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13188 13188 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13188 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13188 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13188 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13188 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159164134663 + 0.011547473376 + (0.008323711851 : ℝ) *
        (1 + 2 * (0.280165913507 + 0.011547473376) / (0.560524820480 * 114.839017759644))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13188]

end BstLean.Part269.N13188

/-! The original eight local profiles supply actual 13188 moment certificates. -/
namespace BstLean.Part269.N13188
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13188 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13188 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13188 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052290989441 ∧
    0 ≤ bN 13188 BstLean.Part154.csC (groupTheta g) ∧ bN 13188 BstLean.Part154.csC (groupTheta g) ≤ 0.001327563324 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13188 13188 0.011
      (momentAllowance 13188 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13188 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13188 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13188 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13188 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13188 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228672231461 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13188 0.011
      (momentAllowance 13188 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13188 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13188
/-! The actual computed-centre upper energy formula at 13188. -/
namespace BstLean.Part269.N13188
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13188

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13188
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13188)
open BstLean.Part268 (cell13188)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084181307042
  | 2 => 0.085103948646
  | 3 => 0.086021922865
  | 4 => 0.086935986073
  | 5 => 0.087847071611
  | 6 => 0.088756318298
  | 7 => 0.089665102060
  | 8 => 0.090575070781
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13188 13188 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13188 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13188

/-! Actual upper energy certificates on all 43 source endpoints at 13188. -/
namespace BstLean.Part269.N13188
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13188)
open BstLean.Part268 (cell13188)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13188 (gMinus 13188) (1 - (cell13188 i).lower) ≤ 1 ∧
    energyUpper 13188 (gMinus 13188) (BstLean.Part211.gPlus 13188)
      (finiteEnergy 13188 13188 0.011) (1 - (cell13188 i).lower) ≤
      (cell13188 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨10,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨11,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨12,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨13,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨14,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨15,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨16,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨17,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨18,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨19,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨20,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨21,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨22,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨23,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨24,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨25,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨26,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨27,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨28,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨29,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨30,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨31,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨32,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨33,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨34,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨35,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨36,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨37,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨38,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨39,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨40,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨41,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨42,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨43,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨44,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨45,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨46,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨47,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨48,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨49,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨50,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨51,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13188) (by norm_num)
        (q := 1 - (cell13188 ⟨52,by decide⟩).lower)
        (by norm_num [cell13188]) (by norm_num [cell13188])
      exact ⟨E.1,E.2.trans (by norm_num [cell13188])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13188

/-! Source-cell containment and simple scalar guards at 13188. -/
namespace BstLean.Part269.N13188
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13188)
open BstLean.Part268 (cell13188)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13188 ⟨10,by decide⟩).lower ∧ (cell13188 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13188 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13188 ⟨11,by decide⟩).lower ∧ (cell13188 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13188 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13188 ⟨12,by decide⟩).lower ∧ (cell13188 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13188 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13188 ⟨13,by decide⟩).lower ∧ (cell13188 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13188 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13188 ⟨14,by decide⟩).lower ∧ (cell13188 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13188 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13188 ⟨15,by decide⟩).lower ∧ (cell13188 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13188 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13188 ⟨16,by decide⟩).lower ∧ (cell13188 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13188 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13188 ⟨17,by decide⟩).lower ∧ (cell13188 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13188 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13188 ⟨18,by decide⟩).lower ∧ (cell13188 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13188 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13188 ⟨19,by decide⟩).lower ∧ (cell13188 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13188 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13188 ⟨20,by decide⟩).lower ∧ (cell13188 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13188 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13188 ⟨21,by decide⟩).lower ∧ (cell13188 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13188 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13188 ⟨22,by decide⟩).lower ∧ (cell13188 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13188 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13188 ⟨23,by decide⟩).lower ∧ (cell13188 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13188 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13188 ⟨24,by decide⟩).lower ∧ (cell13188 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13188 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13188 ⟨25,by decide⟩).lower ∧ (cell13188 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13188 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13188 ⟨26,by decide⟩).lower ∧ (cell13188 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13188 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13188 ⟨27,by decide⟩).lower ∧ (cell13188 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13188 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13188 ⟨28,by decide⟩).lower ∧ (cell13188 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13188 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13188 ⟨29,by decide⟩).lower ∧ (cell13188 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13188 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13188 ⟨30,by decide⟩).lower ∧ (cell13188 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13188 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13188 ⟨31,by decide⟩).lower ∧ (cell13188 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13188 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13188 ⟨32,by decide⟩).lower ∧ (cell13188 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13188 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13188 ⟨33,by decide⟩).lower ∧ (cell13188 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13188 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13188 ⟨34,by decide⟩).lower ∧ (cell13188 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13188 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13188 ⟨35,by decide⟩).lower ∧ (cell13188 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13188 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13188 ⟨36,by decide⟩).lower ∧ (cell13188 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13188 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13188 ⟨37,by decide⟩).lower ∧ (cell13188 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13188 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13188 ⟨38,by decide⟩).lower ∧ (cell13188 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13188 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13188 ⟨39,by decide⟩).lower ∧ (cell13188 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13188 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13188 ⟨40,by decide⟩).lower ∧ (cell13188 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13188 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13188 ⟨41,by decide⟩).lower ∧ (cell13188 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13188 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13188 ⟨42,by decide⟩).lower ∧ (cell13188 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13188 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13188 ⟨43,by decide⟩).lower ∧ (cell13188 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13188 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13188 ⟨44,by decide⟩).lower ∧ (cell13188 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13188 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13188 ⟨45,by decide⟩).lower ∧ (cell13188 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13188 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13188 ⟨46,by decide⟩).lower ∧ (cell13188 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13188 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13188 ⟨47,by decide⟩).lower ∧ (cell13188 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13188 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13188 ⟨48,by decide⟩).lower ∧ (cell13188 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13188 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13188 ⟨49,by decide⟩).lower ∧ (cell13188 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13188 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13188 ⟨50,by decide⟩).lower ∧ (cell13188 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13188 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13188 ⟨51,by decide⟩).lower ∧ (cell13188 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13188 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13188 ⟨52,by decide⟩).lower ∧ (cell13188 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13188 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13188 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13188 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13188,cell13188,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13188 i).lower ∧
    (cell13188 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13188 i).upper ≤ (0.532 : ℝ) ∧
    (cell13188 i).centre ≤ (0.1 : ℝ) ∧ (cell13188 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13188 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13188 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13188

/-! The local source numeric instances at 13188 have no network premises. -/
namespace BstLean.Part269.N13188
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13188)
open BstLean.Part268 (cell13188)

noncomputable def sourceNumerics13188 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13188 (cell13188 i)
      scalarRow13188.M scalarRow13188.H scalarRow13188.xi := by
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
    energy_allowance := scalarRow13188.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13188]
    centre_nonneg := (scalarRow13188.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13188])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13188
/-! Actual 13189 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13189
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13189 ≤ (1.035133329775 : ℝ) := by
  have hr : (114.843371598016 : ℝ) ≤ √(13189 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.843371598016 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13189 13189 (11 / 1000) ≤
    (0.008323396288 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13189) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.843371598016 : ℝ) ≤ √(13189 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13189)
  have hdiv : K / √(13189 : ℝ) ≤ K / 114.843371598016 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.843371598016 ≤ (0.008323396288 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13189.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13189 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13189 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13189 := gPlus_lower 13189
end BstLean.Part269.N13189

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13189
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035133329774 : ℝ) ≤ wn 13189 := by
  have hn : √(13189 : ℝ) ≤ 114.843371598017 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13189 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.843371598017 ≤ 2 / √(13189 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242383781 : ℝ) ≤ rhoBar 13189 BstLean.Part154.csC ∧
    rhoBar 13189 BstLean.Part154.csC ≤ 0.000242384156 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035133329774 : ℝ) / (1.295212 * 13189) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035133329775 : ℝ) / (1.29521 * 13189) := by gcongr
      _ ≤ (0.000242384156 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13189 BstLean.Part154.csC) ≤ 0.000969595375 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13189 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13189 BstLean.Part154.csC) (piBar (rhoBar 13189 BstLean.Part154.csC)) ≤ 0.000185134329 ∧
    cc1 (rhoBar 13189 BstLean.Part154.csC) (piBar (rhoBar 13189 BstLean.Part154.csC)) ≤ 0.000117802270 ∧
    cc2 (rhoBar 13189 BstLean.Part154.csC) ≤ 0.000068385201 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13189 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13189 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13189 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13189 BstLean.Part154.csC * nuR (rhoBar 13189 BstLean.Part154.csC)) ≤ 0.000484783000 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242384156 : ℝ) * 0.000969595375 := by gcongr
      _ ≤ (0.000484783000 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13189 BstLean.Part154.csC) * nuR (rhoBar 13189 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000969595375 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13189 BstLean.Part154.csC) * rhoBar 13189 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242384156 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242384156 / 2 + 0.399 * 0.000969595375 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185134329 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484783000 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117802270 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242384156 / 1.414213562 := by gcongr
      _ ≤ (0.000068385201 : ℝ) := by norm_num

end BstLean.Part269.N13189

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13189
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13189 BstLean.Part154.csC) (piBar (rhoBar 13189 BstLean.Part154.csC)) ≤ 1.48016E-7 := by
  have hr0 : 0 ≤ rhoBar 13189 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13189 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13189 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13189 BstLean.Part154.csC) (piBar (rhoBar 13189 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13189 BstLean.Part154.csC) (piBar (rhoBar 13189 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13189 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185134329 : ℝ) ^ 2 + 0.000117802270 ^ 2 + 3 * 0.000068385201 ^ 2 +
        2 * 0.797885 * 0.000185134329 * 0.000117802270 + 2 * 0.000185134329 * 0.000068385201 +
        4 * 0.797885 * 0.000117802270 * 0.000068385201 := by gcongr
    _ ≤ (1.48016E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13189 BstLean.Part154.csC Θ ≤ 0.002528490881 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13189 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13189 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13189 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13189 BstLean.Part154.csC) (piBar (rhoBar 13189 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13189 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035133329775 * 1.48016E-7 / (0.000242383781 : ℝ) := by gcongr
    _ ≤ 0.002528490881 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13189 BstLean.Part154.csC Θ ≤ 0.002803671530 + 0.000638911529 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13189 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13189 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13189 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035133329775 : ℝ) * ((2 * Θ * 0.000242384156 +
        (6863 / 10000) * 0.000242384156 * 13189 * 0.000969595375) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002803671530 + 0.000638911529 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13189 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13189 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13189 0.011 Θ ∧ gammaRatio 13189 0.011 Θ ≤ 0.000083325405 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13189 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035133329775 : ℝ) * 0.525 / ((1 - 0.011) * 13189) := by gcongr
      _ ≤ (0.000083325405 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13189 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13189 0.011 Θ) :=
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
    badAllowance 13189 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13189 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13189 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13189 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13189 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13189 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13189 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13189 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13189 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13189 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13189 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035133329775 : ℝ) * 13189 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13189 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003121147730 + 0.003167402410 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13189

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13189
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13189 BstLean.Part154.csC) (piBar (rhoBar 13189 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13189 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13189 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13189 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13189 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13189 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13189 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13189 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13189 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13189 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13189 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13189 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13189 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13189 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13189 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051491709089 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13189) ≤ 0.010398837691 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13189 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035133329775)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010398837691 + 2 * 0.737676 / 13189) := by gcongr
    _ ≤ (0.051491709089 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13189 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13189

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13189
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524862415 : ℝ) ≤ plow 13189 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13189) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052290633996)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327457713) : eMP 13189 0.011 xi bn ≤ 0.001143460258 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13189 : ℝ) * (1 - 0.011))) ≤ 0.000565433100 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001327457713 / (13189 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565433100 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565433100 : ℝ) + 3.141593 * 0.052290633996 / (13189 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001143460258 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052290633996)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327457713) : PiBarMP 13189 12 0.011 xi bn ≤ 0.158204063500 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13189 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036434293091 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.209986428508 : ℝ) ≤ √((13189 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.843371598016 : ℝ) ≤ √(13189 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13189) ≤ 0.121316607732 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036434293091 + 0.052290633996 * 1.772454 / (2 * (114.209986428508 : ℝ))) * (1 + 0.001143460258) +
        8 / (13189 * 114.843371598016) + 0.121316607732 := by gcongr
    _ ≤ (0.158204063500 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052290633996)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327457713) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280163163355) :
    parallelOracle 13189 0.011 xi bn cd ≤ 0.159157997439 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13189 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13189 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524862415 : ℝ) ≤ plow 13189 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.843371598016 : ℝ) ≤ √(13189 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280163163355 : ℝ) / (2 * 0.560524862415 * 114.843371598016)) * 0.158204063500 +
        0.280163163355 ^ 2 / (2 * 0.560524862415 * 114.843371598016) := by gcongr
    _ ≤ (0.159157997439 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052290633996) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327457713)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280163163355) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13189 13189 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524862415 : ℝ) ≤ plow 13189 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.843371598016 : ℝ) ≤ √(13189 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13189 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13189 Θ 1.22 ≤ 0.011547035598 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.843371598016 := by gcongr <;> linarith
      _ ≤ (0.011547035598 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13189 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13189 13189 0.011 ≤ 0.008323396288 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13189 13189 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13189 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13189 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13189 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13189 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159157997439 + 0.011547035598 + (0.008323396288 : ℝ) *
        (1 + 2 * (0.280163163355 + 0.011547035598) / (0.560524862415 * 114.843371598016))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13189]

end BstLean.Part269.N13189

/-! The original eight local profiles supply actual 13189 moment certificates. -/
namespace BstLean.Part269.N13189
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13189 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13189 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13189 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052290633996 ∧
    0 ≤ bN 13189 BstLean.Part154.csC (groupTheta g) ∧ bN 13189 BstLean.Part154.csC (groupTheta g) ≤ 0.001327457713 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13189 13189 0.011
      (momentAllowance 13189 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13189 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13189 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13189 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13189 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13189 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228671454266 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13189 0.011
      (momentAllowance 13189 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13189 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13189
/-! The actual computed-centre upper energy formula at 13189. -/
namespace BstLean.Part269.N13189
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13189

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13189
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13189)
open BstLean.Part268 (cell13189)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084178828389
  | 2 => 0.085101440207
  | 3 => 0.086019380533
  | 4 => 0.086933404752
  | 5 => 0.087844445030
  | 6 => 0.088753638801
  | 7 => 0.089662360365
  | 8 => 0.090572255715
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13189 13189 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13189 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13189

/-! Actual upper energy certificates on all 43 source endpoints at 13189. -/
namespace BstLean.Part269.N13189
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13189)
open BstLean.Part268 (cell13189)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13189 (gMinus 13189) (1 - (cell13189 i).lower) ≤ 1 ∧
    energyUpper 13189 (gMinus 13189) (BstLean.Part211.gPlus 13189)
      (finiteEnergy 13189 13189 0.011) (1 - (cell13189 i).lower) ≤
      (cell13189 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨10,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨11,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨12,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨13,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨14,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨15,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨16,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨17,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨18,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨19,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨20,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨21,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨22,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨23,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨24,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨25,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨26,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨27,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨28,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨29,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨30,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨31,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨32,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨33,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨34,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨35,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨36,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨37,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨38,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨39,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨40,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨41,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨42,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨43,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨44,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨45,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨46,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨47,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨48,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨49,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨50,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨51,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13189) (by norm_num)
        (q := 1 - (cell13189 ⟨52,by decide⟩).lower)
        (by norm_num [cell13189]) (by norm_num [cell13189])
      exact ⟨E.1,E.2.trans (by norm_num [cell13189])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13189

/-! Source-cell containment and simple scalar guards at 13189. -/
namespace BstLean.Part269.N13189
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13189)
open BstLean.Part268 (cell13189)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13189 ⟨10,by decide⟩).lower ∧ (cell13189 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13189 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13189 ⟨11,by decide⟩).lower ∧ (cell13189 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13189 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13189 ⟨12,by decide⟩).lower ∧ (cell13189 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13189 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13189 ⟨13,by decide⟩).lower ∧ (cell13189 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13189 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13189 ⟨14,by decide⟩).lower ∧ (cell13189 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13189 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13189 ⟨15,by decide⟩).lower ∧ (cell13189 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13189 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13189 ⟨16,by decide⟩).lower ∧ (cell13189 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13189 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13189 ⟨17,by decide⟩).lower ∧ (cell13189 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13189 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13189 ⟨18,by decide⟩).lower ∧ (cell13189 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13189 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13189 ⟨19,by decide⟩).lower ∧ (cell13189 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13189 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13189 ⟨20,by decide⟩).lower ∧ (cell13189 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13189 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13189 ⟨21,by decide⟩).lower ∧ (cell13189 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13189 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13189 ⟨22,by decide⟩).lower ∧ (cell13189 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13189 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13189 ⟨23,by decide⟩).lower ∧ (cell13189 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13189 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13189 ⟨24,by decide⟩).lower ∧ (cell13189 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13189 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13189 ⟨25,by decide⟩).lower ∧ (cell13189 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13189 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13189 ⟨26,by decide⟩).lower ∧ (cell13189 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13189 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13189 ⟨27,by decide⟩).lower ∧ (cell13189 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13189 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13189 ⟨28,by decide⟩).lower ∧ (cell13189 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13189 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13189 ⟨29,by decide⟩).lower ∧ (cell13189 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13189 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13189 ⟨30,by decide⟩).lower ∧ (cell13189 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13189 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13189 ⟨31,by decide⟩).lower ∧ (cell13189 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13189 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13189 ⟨32,by decide⟩).lower ∧ (cell13189 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13189 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13189 ⟨33,by decide⟩).lower ∧ (cell13189 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13189 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13189 ⟨34,by decide⟩).lower ∧ (cell13189 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13189 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13189 ⟨35,by decide⟩).lower ∧ (cell13189 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13189 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13189 ⟨36,by decide⟩).lower ∧ (cell13189 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13189 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13189 ⟨37,by decide⟩).lower ∧ (cell13189 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13189 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13189 ⟨38,by decide⟩).lower ∧ (cell13189 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13189 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13189 ⟨39,by decide⟩).lower ∧ (cell13189 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13189 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13189 ⟨40,by decide⟩).lower ∧ (cell13189 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13189 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13189 ⟨41,by decide⟩).lower ∧ (cell13189 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13189 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13189 ⟨42,by decide⟩).lower ∧ (cell13189 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13189 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13189 ⟨43,by decide⟩).lower ∧ (cell13189 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13189 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13189 ⟨44,by decide⟩).lower ∧ (cell13189 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13189 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13189 ⟨45,by decide⟩).lower ∧ (cell13189 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13189 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13189 ⟨46,by decide⟩).lower ∧ (cell13189 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13189 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13189 ⟨47,by decide⟩).lower ∧ (cell13189 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13189 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13189 ⟨48,by decide⟩).lower ∧ (cell13189 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13189 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13189 ⟨49,by decide⟩).lower ∧ (cell13189 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13189 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13189 ⟨50,by decide⟩).lower ∧ (cell13189 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13189 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13189 ⟨51,by decide⟩).lower ∧ (cell13189 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13189 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13189 ⟨52,by decide⟩).lower ∧ (cell13189 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13189 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13189 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13189 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13189,cell13189,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13189 i).lower ∧
    (cell13189 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13189 i).upper ≤ (0.532 : ℝ) ∧
    (cell13189 i).centre ≤ (0.1 : ℝ) ∧ (cell13189 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13189 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13189 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13189

/-! The local source numeric instances at 13189 have no network premises. -/
namespace BstLean.Part269.N13189
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13189)
open BstLean.Part268 (cell13189)

noncomputable def sourceNumerics13189 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13189 (cell13189 i)
      scalarRow13189.M scalarRow13189.H scalarRow13189.xi := by
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
    energy_allowance := scalarRow13189.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13189]
    centre_nonneg := (scalarRow13189.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13189])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13189
/-! Actual 13190 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13190
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13190 ≤ (1.035131986436 : ℝ) := by
  have hr : (114.847725271334 : ℝ) ≤ √(13190 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.847725271334 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13190 13190 (11 / 1000) ≤
    (0.008323080761 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13190) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.847725271334 : ℝ) ≤ √(13190 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13190)
  have hdiv : K / √(13190 : ℝ) ≤ K / 114.847725271334 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.847725271334 ≤ (0.008323080761 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13190.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13190 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13190 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13190 := gPlus_lower 13190
end BstLean.Part269.N13190

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13190
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035131986435 : ℝ) ≤ wn 13190 := by
  have hn : √(13190 : ℝ) ≤ 114.847725271335 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13190 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.847725271335 ≤ 2 / √(13190 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242365090 : ℝ) ≤ rhoBar 13190 BstLean.Part154.csC ∧
    rhoBar 13190 BstLean.Part154.csC ≤ 0.000242365465 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035131986435 : ℝ) / (1.295212 * 13190) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035131986436 : ℝ) / (1.29521 * 13190) := by gcongr
      _ ≤ (0.000242365465 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13190 BstLean.Part154.csC) ≤ 0.000969520602 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13190 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13190 BstLean.Part154.csC) (piBar (rhoBar 13190 BstLean.Part154.csC)) ≤ 0.000185120052 ∧
    cc1 (rhoBar 13190 BstLean.Part154.csC) (piBar (rhoBar 13190 BstLean.Part154.csC)) ≤ 0.000117793185 ∧
    cc2 (rhoBar 13190 BstLean.Part154.csC) ≤ 0.000068379928 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13190 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13190 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13190 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13190 BstLean.Part154.csC * nuR (rhoBar 13190 BstLean.Part154.csC)) ≤ 0.000484745616 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242365465 : ℝ) * 0.000969520602 := by gcongr
      _ ≤ (0.000484745616 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13190 BstLean.Part154.csC) * nuR (rhoBar 13190 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000969520602 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13190 BstLean.Part154.csC) * rhoBar 13190 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242365465 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242365465 / 2 + 0.399 * 0.000969520602 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185120052 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484745616 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117793185 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242365465 / 1.414213562 := by gcongr
      _ ≤ (0.000068379928 : ℝ) := by norm_num

end BstLean.Part269.N13190

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13190
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13190 BstLean.Part154.csC) (piBar (rhoBar 13190 BstLean.Part154.csC)) ≤ 1.47994E-7 := by
  have hr0 : 0 ≤ rhoBar 13190 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13190 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13190 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13190 BstLean.Part154.csC) (piBar (rhoBar 13190 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13190 BstLean.Part154.csC) (piBar (rhoBar 13190 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13190 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185120052 : ℝ) ^ 2 + 0.000117793185 ^ 2 + 3 * 0.000068379928 ^ 2 +
        2 * 0.797885 * 0.000185120052 * 0.000117793185 + 2 * 0.000185120052 * 0.000068379928 +
        4 * 0.797885 * 0.000117793185 * 0.000068379928 := by gcongr
    _ ≤ (1.47994E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13190 BstLean.Part154.csC Θ ≤ 0.002528306750 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13190 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13190 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13190 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13190 BstLean.Part154.csC) (piBar (rhoBar 13190 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13190 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035131986436 * 1.47994E-7 / (0.000242365090 : ℝ) := by gcongr
    _ ≤ 0.002528306750 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13190 BstLean.Part154.csC Θ ≤ 0.002803448040 + 0.000638861432 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13190 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13190 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13190 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035131986436 : ℝ) * ((2 * Θ * 0.000242365465 +
        (6863 / 10000) * 0.000242365465 * 13190 * 0.000969520602) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002803448040 + 0.000638861432 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13190 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13190 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13190 0.011 Θ ∧ gammaRatio 13190 0.011 Θ ≤ 0.000083318980 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13190 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035131986436 : ℝ) * 0.525 / ((1 - 0.011) * 13190) := by gcongr
      _ ≤ (0.000083318980 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13190 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13190 0.011 Θ) :=
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
    badAllowance 13190 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13190 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13190 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13190 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13190 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13190 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13190 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13190 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13190 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13190 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13190 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035131986436 : ℝ) * 13190 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13190 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003120924240 + 0.003167168182 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13190

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13190
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13190 BstLean.Part154.csC) (piBar (rhoBar 13190 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13190 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13190 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13190 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13190 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13190 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13190 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13190 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13190 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13190 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13190 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13190 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13190 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13190 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13190 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051489736354 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13190) ≤ 0.010398443489 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13190 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035131986436)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010398443489 + 2 * 0.737676 / 13190) := by gcongr
    _ ≤ (0.051489736354 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13190 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13190

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13190
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524904344 : ℝ) ≤ plow 13190 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13190) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052290287536)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327361044) : eMP 13190 0.011 xi bn ≤ 0.001143375176 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13190 : ℝ) * (1 - 0.011))) ≤ 0.000565391078 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001327361044 / (13190 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565391078 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565391078 : ℝ) + 3.141593 * 0.052290287536 / (13190 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001143375176 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052290287536)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327361044) : PiBarMP 13190 12 0.011 xi bn ≤ 0.158198114616 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13190 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036432966446 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.214316090409 : ℝ) ≤ √((13190 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.847725271334 : ℝ) ≤ √(13190 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13190) ≤ 0.121312008835 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036432966446 + 0.052290287536 * 1.772454 / (2 * (114.214316090409 : ℝ))) * (1 + 0.001143375176) +
        8 / (13190 * 114.847725271334) + 0.121312008835 := by gcongr
    _ ≤ (0.158198114616 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052290287536)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327361044) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280160433069) :
    parallelOracle 13190 0.011 xi bn cd ≤ 0.159151984139 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13190 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13190 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524904344 : ℝ) ≤ plow 13190 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.847725271334 : ℝ) ≤ √(13190 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280160433069 : ℝ) / (2 * 0.560524904344 * 114.847725271334)) * 0.158198114616 +
        0.280160433069 ^ 2 / (2 * 0.560524904344 * 114.847725271334) := by gcongr
    _ ≤ (0.159151984139 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052290287536) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327361044)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280160433069) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13190 13190 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524904344 : ℝ) ≤ plow 13190 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.847725271334 : ℝ) ≤ √(13190 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13190 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13190 Θ 1.22 ≤ 0.011546597871 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.847725271334 := by gcongr <;> linarith
      _ ≤ (0.011546597871 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13190 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13190 13190 0.011 ≤ 0.008323080761 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13190 13190 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13190 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13190 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13190 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13190 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159151984139 + 0.011546597871 + (0.008323080761 : ℝ) *
        (1 + 2 * (0.280160433069 + 0.011546597871) / (0.560524904344 * 114.847725271334))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13190]

end BstLean.Part269.N13190

/-! The original eight local profiles supply actual 13190 moment certificates. -/
namespace BstLean.Part269.N13190
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13190 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13190 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13190 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052290287536 ∧
    0 ≤ bN 13190 BstLean.Part154.csC (groupTheta g) ∧ bN 13190 BstLean.Part154.csC (groupTheta g) ≤ 0.001327361044 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13190 13190 0.011
      (momentAllowance 13190 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13190 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13190 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13190 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13190 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13190 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228670696715 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13190 0.011
      (momentAllowance 13190 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13190 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13190
/-! The actual computed-centre upper energy formula at 13190. -/
namespace BstLean.Part269.N13190
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13190

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13190
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13190)
open BstLean.Part268 (cell13190)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084176350418
  | 2 => 0.085098932472
  | 3 => 0.086016838933
  | 4 => 0.086930824197
  | 5 => 0.087841819258
  | 6 => 0.088750960163
  | 7 => 0.089659619593
  | 8 => 0.090569441649
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13190 13190 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13190 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13190

/-! Actual upper energy certificates on all 43 source endpoints at 13190. -/
namespace BstLean.Part269.N13190
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13190)
open BstLean.Part268 (cell13190)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13190 (gMinus 13190) (1 - (cell13190 i).lower) ≤ 1 ∧
    energyUpper 13190 (gMinus 13190) (BstLean.Part211.gPlus 13190)
      (finiteEnergy 13190 13190 0.011) (1 - (cell13190 i).lower) ≤
      (cell13190 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨10,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨11,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨12,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨13,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨14,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨15,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨16,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨17,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨18,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨19,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨20,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨21,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨22,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨23,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨24,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨25,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨26,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨27,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨28,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨29,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨30,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨31,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨32,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨33,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨34,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨35,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨36,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨37,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨38,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨39,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨40,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨41,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨42,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨43,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨44,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨45,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨46,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨47,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨48,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨49,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨50,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨51,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13190) (by norm_num)
        (q := 1 - (cell13190 ⟨52,by decide⟩).lower)
        (by norm_num [cell13190]) (by norm_num [cell13190])
      exact ⟨E.1,E.2.trans (by norm_num [cell13190])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13190

/-! Source-cell containment and simple scalar guards at 13190. -/
namespace BstLean.Part269.N13190
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13190)
open BstLean.Part268 (cell13190)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13190 ⟨10,by decide⟩).lower ∧ (cell13190 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13190 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13190 ⟨11,by decide⟩).lower ∧ (cell13190 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13190 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13190 ⟨12,by decide⟩).lower ∧ (cell13190 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13190 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13190 ⟨13,by decide⟩).lower ∧ (cell13190 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13190 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13190 ⟨14,by decide⟩).lower ∧ (cell13190 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13190 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13190 ⟨15,by decide⟩).lower ∧ (cell13190 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13190 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13190 ⟨16,by decide⟩).lower ∧ (cell13190 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13190 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13190 ⟨17,by decide⟩).lower ∧ (cell13190 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13190 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13190 ⟨18,by decide⟩).lower ∧ (cell13190 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13190 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13190 ⟨19,by decide⟩).lower ∧ (cell13190 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13190 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13190 ⟨20,by decide⟩).lower ∧ (cell13190 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13190 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13190 ⟨21,by decide⟩).lower ∧ (cell13190 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13190 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13190 ⟨22,by decide⟩).lower ∧ (cell13190 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13190 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13190 ⟨23,by decide⟩).lower ∧ (cell13190 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13190 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13190 ⟨24,by decide⟩).lower ∧ (cell13190 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13190 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13190 ⟨25,by decide⟩).lower ∧ (cell13190 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13190 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13190 ⟨26,by decide⟩).lower ∧ (cell13190 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13190 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13190 ⟨27,by decide⟩).lower ∧ (cell13190 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13190 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13190 ⟨28,by decide⟩).lower ∧ (cell13190 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13190 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13190 ⟨29,by decide⟩).lower ∧ (cell13190 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13190 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13190 ⟨30,by decide⟩).lower ∧ (cell13190 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13190 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13190 ⟨31,by decide⟩).lower ∧ (cell13190 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13190 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13190 ⟨32,by decide⟩).lower ∧ (cell13190 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13190 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13190 ⟨33,by decide⟩).lower ∧ (cell13190 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13190 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13190 ⟨34,by decide⟩).lower ∧ (cell13190 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13190 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13190 ⟨35,by decide⟩).lower ∧ (cell13190 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13190 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13190 ⟨36,by decide⟩).lower ∧ (cell13190 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13190 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13190 ⟨37,by decide⟩).lower ∧ (cell13190 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13190 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13190 ⟨38,by decide⟩).lower ∧ (cell13190 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13190 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13190 ⟨39,by decide⟩).lower ∧ (cell13190 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13190 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13190 ⟨40,by decide⟩).lower ∧ (cell13190 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13190 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13190 ⟨41,by decide⟩).lower ∧ (cell13190 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13190 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13190 ⟨42,by decide⟩).lower ∧ (cell13190 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13190 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13190 ⟨43,by decide⟩).lower ∧ (cell13190 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13190 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13190 ⟨44,by decide⟩).lower ∧ (cell13190 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13190 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13190 ⟨45,by decide⟩).lower ∧ (cell13190 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13190 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13190 ⟨46,by decide⟩).lower ∧ (cell13190 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13190 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13190 ⟨47,by decide⟩).lower ∧ (cell13190 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13190 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13190 ⟨48,by decide⟩).lower ∧ (cell13190 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13190 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13190 ⟨49,by decide⟩).lower ∧ (cell13190 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13190 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13190 ⟨50,by decide⟩).lower ∧ (cell13190 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13190 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13190 ⟨51,by decide⟩).lower ∧ (cell13190 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13190 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13190 ⟨52,by decide⟩).lower ∧ (cell13190 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13190 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13190 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13190 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13190,cell13190,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13190 i).lower ∧
    (cell13190 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13190 i).upper ≤ (0.532 : ℝ) ∧
    (cell13190 i).centre ≤ (0.1 : ℝ) ∧ (cell13190 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13190 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13190 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13190

/-! The local source numeric instances at 13190 have no network premises. -/
namespace BstLean.Part269.N13190
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13190)
open BstLean.Part268 (cell13190)

noncomputable def sourceNumerics13190 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13190 (cell13190 i)
      scalarRow13190.M scalarRow13190.H scalarRow13190.xi := by
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
    energy_allowance := scalarRow13190.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13190]
    centre_nonneg := (scalarRow13190.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13190])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13190
/-! Actual 13191 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13191
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13191 ≤ (1.035130643251 : ℝ) := by
  have hr : (114.852078779619 : ℝ) ≤ √(13191 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.852078779619 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13191 13191 (11 / 1000) ≤
    (0.008322765269 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13191) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.852078779619 : ℝ) ≤ √(13191 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13191)
  have hdiv : K / √(13191 : ℝ) ≤ K / 114.852078779619 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.852078779619 ≤ (0.008322765269 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13191.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13191 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13191 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13191 := gPlus_lower 13191
end BstLean.Part269.N13191

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13191
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035130643250 : ℝ) ≤ wn 13191 := by
  have hn : √(13191 : ℝ) ≤ 114.852078779620 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13191 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.852078779620 ≤ 2 / √(13191 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242346402 : ℝ) ≤ rhoBar 13191 BstLean.Part154.csC ∧
    rhoBar 13191 BstLean.Part154.csC ≤ 0.000242346777 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035130643250 : ℝ) / (1.295212 * 13191) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035130643251 : ℝ) / (1.29521 * 13191) := by gcongr
      _ ≤ (0.000242346777 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13191 BstLean.Part154.csC) ≤ 0.000969445840 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13191 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13191 BstLean.Part154.csC) (piBar (rhoBar 13191 BstLean.Part154.csC)) ≤ 0.000185105777 ∧
    cc1 (rhoBar 13191 BstLean.Part154.csC) (piBar (rhoBar 13191 BstLean.Part154.csC)) ≤ 0.000117784102 ∧
    cc2 (rhoBar 13191 BstLean.Part154.csC) ≤ 0.000068374655 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13191 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13191 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13191 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13191 BstLean.Part154.csC * nuR (rhoBar 13191 BstLean.Part154.csC)) ≤ 0.000484708237 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242346777 : ℝ) * 0.000969445840 := by gcongr
      _ ≤ (0.000484708237 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13191 BstLean.Part154.csC) * nuR (rhoBar 13191 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000969445840 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13191 BstLean.Part154.csC) * rhoBar 13191 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242346777 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242346777 / 2 + 0.399 * 0.000969445840 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185105777 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484708237 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117784102 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242346777 / 1.414213562 := by gcongr
      _ ≤ (0.000068374655 : ℝ) := by norm_num

end BstLean.Part269.N13191

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13191
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13191 BstLean.Part154.csC) (piBar (rhoBar 13191 BstLean.Part154.csC)) ≤ 1.47971E-7 := by
  have hr0 : 0 ≤ rhoBar 13191 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13191 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13191 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13191 BstLean.Part154.csC) (piBar (rhoBar 13191 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13191 BstLean.Part154.csC) (piBar (rhoBar 13191 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13191 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185105777 : ℝ) ^ 2 + 0.000117784102 ^ 2 + 3 * 0.000068374655 ^ 2 +
        2 * 0.797885 * 0.000185105777 * 0.000117784102 + 2 * 0.000185105777 * 0.000068374655 +
        4 * 0.797885 * 0.000117784102 * 0.000068374655 := by gcongr
    _ ≤ (1.47971E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13191 BstLean.Part154.csC Θ ≤ 0.002528105475 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13191 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13191 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13191 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13191 BstLean.Part154.csC) (piBar (rhoBar 13191 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13191 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035130643251 * 1.47971E-7 / (0.000242346402 : ℝ) := by gcongr
    _ ≤ 0.002528105475 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13191 BstLean.Part154.csC Θ ≤ 0.002803224585 + 0.000638811342 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13191 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13191 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13191 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035130643251 : ℝ) * ((2 * Θ * 0.000242346777 +
        (6863 / 10000) * 0.000242346777 * 13191 * 0.000969445840) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002803224585 + 0.000638811342 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13191 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13191 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13191 0.011 Θ ∧ gammaRatio 13191 0.011 Θ ≤ 0.000083312555 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13191 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035130643251 : ℝ) * 0.525 / ((1 - 0.011) * 13191) := by gcongr
      _ ≤ (0.000083312555 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13191 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13191 0.011 Θ) :=
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
    badAllowance 13191 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13191 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13191 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13191 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13191 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13191 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13191 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13191 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13191 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13191 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13191 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035130643251 : ℝ) * 13191 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13191 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003120700785 + 0.003166916817 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13191

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13191
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13191 BstLean.Part154.csC) (piBar (rhoBar 13191 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13191 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13191 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13191 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13191 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13191 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13191 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13191 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13191 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13191 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13191 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13191 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13191 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13191 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13191 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051487763850 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13191) ≤ 0.010398049333 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13191 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035130643251)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010398049333 + 2 * 0.737676 / 13191) := by gcongr
    _ ≤ (0.051487763850 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13191 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13191

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13191
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524946266 : ℝ) ≤ plow 13191 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13191) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052289932114)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327255375) : eMP 13191 0.011 xi bn ≤ 0.001143286263 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13191 : ℝ) * (1 - 0.011))) ≤ 0.000565347142 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001327255375 / (13191 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565347142 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565347142 : ℝ) + 3.141593 * 0.052289932114 / (13191 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001143286263 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052289932114)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327255375) : PiBarMP 13191 12 0.011 xi bn ≤ 0.158192042337 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13191 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036431516233 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.218645588187 : ℝ) ≤ √((13191 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.852078779619 : ℝ) ≤ √(13191 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13191) ≤ 0.121307410461 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036431516233 + 0.052289932114 * 1.772454 / (2 * (114.218645588187 : ℝ))) * (1 + 0.001143286263) +
        8 / (13191 * 114.852078779619) + 0.121307410461 := by gcongr
    _ ≤ (0.158192042337 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052289932114)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327255375) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280157683416) :
    parallelOracle 13191 0.011 xi bn cd ≤ 0.159145847075 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13191 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13191 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524946266 : ℝ) ≤ plow 13191 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.852078779619 : ℝ) ≤ √(13191 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280157683416 : ℝ) / (2 * 0.560524946266 * 114.852078779619)) * 0.158192042337 +
        0.280157683416 ^ 2 / (2 * 0.560524946266 * 114.852078779619) := by gcongr
    _ ≤ (0.159145847075 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052289932114) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327255375)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280157683416) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13191 13191 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524946266 : ℝ) ≤ plow 13191 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.852078779619 : ℝ) ≤ √(13191 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13191 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13191 Θ 1.22 ≤ 0.011546160193 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.852078779619 := by gcongr <;> linarith
      _ ≤ (0.011546160193 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13191 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13191 13191 0.011 ≤ 0.008322765269 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13191 13191 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13191 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13191 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13191 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13191 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159145847075 + 0.011546160193 + (0.008322765269 : ℝ) *
        (1 + 2 * (0.280157683416 + 0.011546160193) / (0.560524946266 * 114.852078779619))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13191]

end BstLean.Part269.N13191

/-! The original eight local profiles supply actual 13191 moment certificates. -/
namespace BstLean.Part269.N13191
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13191 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13191 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13191 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052289932114 ∧
    0 ≤ bN 13191 BstLean.Part154.csC (groupTheta g) ∧ bN 13191 BstLean.Part154.csC (groupTheta g) ≤ 0.001327255375 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13191 13191 0.011
      (momentAllowance 13191 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13191 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13191 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13191 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13191 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13191 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228669919566 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13191 0.011
      (momentAllowance 13191 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13191 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13191
/-! The actual computed-centre upper energy formula at 13191. -/
namespace BstLean.Part269.N13191
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13191

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13191
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13191)
open BstLean.Part268 (cell13191)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084173873129
  | 2 => 0.085096425441
  | 3 => 0.086014298065
  | 4 => 0.086928244409
  | 5 => 0.087839194294
  | 6 => 0.088748282386
  | 7 => 0.089656879743
  | 8 => 0.090566628581
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13191 13191 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13191 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13191

/-! Actual upper energy certificates on all 43 source endpoints at 13191. -/
namespace BstLean.Part269.N13191
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13191)
open BstLean.Part268 (cell13191)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13191 (gMinus 13191) (1 - (cell13191 i).lower) ≤ 1 ∧
    energyUpper 13191 (gMinus 13191) (BstLean.Part211.gPlus 13191)
      (finiteEnergy 13191 13191 0.011) (1 - (cell13191 i).lower) ≤
      (cell13191 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨10,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨11,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨12,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨13,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨14,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨15,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨16,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨17,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨18,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨19,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨20,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨21,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨22,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨23,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨24,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨25,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨26,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨27,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨28,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨29,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨30,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨31,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨32,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨33,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨34,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨35,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨36,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨37,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨38,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨39,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨40,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨41,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨42,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨43,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨44,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨45,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨46,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨47,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨48,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨49,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨50,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨51,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13191) (by norm_num)
        (q := 1 - (cell13191 ⟨52,by decide⟩).lower)
        (by norm_num [cell13191]) (by norm_num [cell13191])
      exact ⟨E.1,E.2.trans (by norm_num [cell13191])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13191

/-! Source-cell containment and simple scalar guards at 13191. -/
namespace BstLean.Part269.N13191
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13191)
open BstLean.Part268 (cell13191)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13191 ⟨10,by decide⟩).lower ∧ (cell13191 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13191 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13191 ⟨11,by decide⟩).lower ∧ (cell13191 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13191 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13191 ⟨12,by decide⟩).lower ∧ (cell13191 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13191 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13191 ⟨13,by decide⟩).lower ∧ (cell13191 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13191 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13191 ⟨14,by decide⟩).lower ∧ (cell13191 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13191 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13191 ⟨15,by decide⟩).lower ∧ (cell13191 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13191 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13191 ⟨16,by decide⟩).lower ∧ (cell13191 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13191 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13191 ⟨17,by decide⟩).lower ∧ (cell13191 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13191 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13191 ⟨18,by decide⟩).lower ∧ (cell13191 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13191 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13191 ⟨19,by decide⟩).lower ∧ (cell13191 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13191 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13191 ⟨20,by decide⟩).lower ∧ (cell13191 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13191 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13191 ⟨21,by decide⟩).lower ∧ (cell13191 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13191 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13191 ⟨22,by decide⟩).lower ∧ (cell13191 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13191 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13191 ⟨23,by decide⟩).lower ∧ (cell13191 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13191 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13191 ⟨24,by decide⟩).lower ∧ (cell13191 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13191 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13191 ⟨25,by decide⟩).lower ∧ (cell13191 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13191 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13191 ⟨26,by decide⟩).lower ∧ (cell13191 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13191 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13191 ⟨27,by decide⟩).lower ∧ (cell13191 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13191 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13191 ⟨28,by decide⟩).lower ∧ (cell13191 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13191 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13191 ⟨29,by decide⟩).lower ∧ (cell13191 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13191 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13191 ⟨30,by decide⟩).lower ∧ (cell13191 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13191 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13191 ⟨31,by decide⟩).lower ∧ (cell13191 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13191 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13191 ⟨32,by decide⟩).lower ∧ (cell13191 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13191 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13191 ⟨33,by decide⟩).lower ∧ (cell13191 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13191 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13191 ⟨34,by decide⟩).lower ∧ (cell13191 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13191 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13191 ⟨35,by decide⟩).lower ∧ (cell13191 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13191 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13191 ⟨36,by decide⟩).lower ∧ (cell13191 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13191 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13191 ⟨37,by decide⟩).lower ∧ (cell13191 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13191 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13191 ⟨38,by decide⟩).lower ∧ (cell13191 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13191 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13191 ⟨39,by decide⟩).lower ∧ (cell13191 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13191 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13191 ⟨40,by decide⟩).lower ∧ (cell13191 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13191 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13191 ⟨41,by decide⟩).lower ∧ (cell13191 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13191 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13191 ⟨42,by decide⟩).lower ∧ (cell13191 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13191 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13191 ⟨43,by decide⟩).lower ∧ (cell13191 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13191 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13191 ⟨44,by decide⟩).lower ∧ (cell13191 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13191 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13191 ⟨45,by decide⟩).lower ∧ (cell13191 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13191 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13191 ⟨46,by decide⟩).lower ∧ (cell13191 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13191 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13191 ⟨47,by decide⟩).lower ∧ (cell13191 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13191 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13191 ⟨48,by decide⟩).lower ∧ (cell13191 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13191 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13191 ⟨49,by decide⟩).lower ∧ (cell13191 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13191 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13191 ⟨50,by decide⟩).lower ∧ (cell13191 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13191 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13191 ⟨51,by decide⟩).lower ∧ (cell13191 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13191 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13191 ⟨52,by decide⟩).lower ∧ (cell13191 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13191 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13191 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13191 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13191,cell13191,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13191 i).lower ∧
    (cell13191 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13191 i).upper ≤ (0.532 : ℝ) ∧
    (cell13191 i).centre ≤ (0.1 : ℝ) ∧ (cell13191 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13191 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13191 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13191

/-! The local source numeric instances at 13191 have no network premises. -/
namespace BstLean.Part269.N13191
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13191)
open BstLean.Part268 (cell13191)

noncomputable def sourceNumerics13191 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13191 (cell13191 i)
      scalarRow13191.M scalarRow13191.H scalarRow13191.xi := by
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
    energy_allowance := scalarRow13191.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13191]
    centre_nonneg := (scalarRow13191.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13191])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13191
/-! Actual 13192 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13192
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13192 ≤ (1.035129300220 : ℝ) := by
  have hr : (114.856432122889 : ℝ) ≤ √(13192 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.856432122889 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13192 13192 (11 / 1000) ≤
    (0.008322449813 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13192) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.856432122889 : ℝ) ≤ √(13192 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13192)
  have hdiv : K / √(13192 : ℝ) ≤ K / 114.856432122889 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.856432122889 ≤ (0.008322449813 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13192.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13192 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13192 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13192 := gPlus_lower 13192
end BstLean.Part269.N13192

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13192
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035129300219 : ℝ) ≤ wn 13192 := by
  have hn : √(13192 : ℝ) ≤ 114.856432122890 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13192 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.856432122890 ≤ 2 / √(13192 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242327717 : ℝ) ≤ rhoBar 13192 BstLean.Part154.csC ∧
    rhoBar 13192 BstLean.Part154.csC ≤ 0.000242328092 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035129300219 : ℝ) / (1.295212 * 13192) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035129300220 : ℝ) / (1.29521 * 13192) := by gcongr
      _ ≤ (0.000242328092 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13192 BstLean.Part154.csC) ≤ 0.000969371091 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13192 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13192 BstLean.Part154.csC) (piBar (rhoBar 13192 BstLean.Part154.csC)) ≤ 0.000185091505 ∧
    cc1 (rhoBar 13192 BstLean.Part154.csC) (piBar (rhoBar 13192 BstLean.Part154.csC)) ≤ 0.000117775021 ∧
    cc2 (rhoBar 13192 BstLean.Part154.csC) ≤ 0.000068369384 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13192 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13192 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13192 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13192 BstLean.Part154.csC * nuR (rhoBar 13192 BstLean.Part154.csC)) ≤ 0.000484670865 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242328092 : ℝ) * 0.000969371091 := by gcongr
      _ ≤ (0.000484670865 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13192 BstLean.Part154.csC) * nuR (rhoBar 13192 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000969371091 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13192 BstLean.Part154.csC) * rhoBar 13192 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242328092 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242328092 / 2 + 0.399 * 0.000969371091 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185091505 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484670865 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117775021 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242328092 / 1.414213562 := by gcongr
      _ ≤ (0.000068369384 : ℝ) := by norm_num

end BstLean.Part269.N13192

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13192
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13192 BstLean.Part154.csC) (piBar (rhoBar 13192 BstLean.Part154.csC)) ≤ 1.47948E-7 := by
  have hr0 : 0 ≤ rhoBar 13192 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13192 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13192 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13192 BstLean.Part154.csC) (piBar (rhoBar 13192 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13192 BstLean.Part154.csC) (piBar (rhoBar 13192 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13192 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185091505 : ℝ) ^ 2 + 0.000117775021 ^ 2 + 3 * 0.000068369384 ^ 2 +
        2 * 0.797885 * 0.000185091505 * 0.000117775021 + 2 * 0.000185091505 * 0.000068369384 +
        4 * 0.797885 * 0.000117775021 * 0.000068369384 := by gcongr
    _ ≤ (1.47948E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13192 BstLean.Part154.csC Θ ≤ 0.002527904140 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13192 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13192 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13192 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13192 BstLean.Part154.csC) (piBar (rhoBar 13192 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13192 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035129300220 * 1.47948E-7 / (0.000242327717 : ℝ) := by gcongr
    _ ≤ 0.002527904140 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13192 BstLean.Part154.csC Θ ≤ 0.002803001171 + 0.000638761261 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13192 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13192 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13192 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035129300220 : ℝ) * ((2 * Θ * 0.000242328092 +
        (6863 / 10000) * 0.000242328092 * 13192 * 0.000969371091) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002803001171 + 0.000638761261 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13192 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13192 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13192 0.011 Θ ∧ gammaRatio 13192 0.011 Θ ≤ 0.000083306132 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13192 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035129300220 : ℝ) * 0.525 / ((1 - 0.011) * 13192) := by gcongr
      _ ≤ (0.000083306132 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13192 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13192 0.011 Θ) :=
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
    badAllowance 13192 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13192 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13192 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13192 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13192 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13192 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13192 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13192 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13192 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13192 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13192 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035129300220 : ℝ) * 13192 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13192 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003120477371 + 0.003166665401 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13192

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13192
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13192 BstLean.Part154.csC) (piBar (rhoBar 13192 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13192 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13192 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13192 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13192 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13192 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13192 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13192 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13192 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13192 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13192 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13192 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13192 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13192 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13192 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051485791569 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13192) ≤ 0.010397655221 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13192 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035129300220)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010397655221 + 2 * 0.737676 / 13192) := by gcongr
    _ ≤ (0.051485791569 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13192 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13192

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13192
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560524988182 : ℝ) ≤ plow 13192 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13192) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052289576707)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327149674) : eMP 13192 0.011 xi bn ≤ 0.001143197345 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13192 : ℝ) * (1 - 0.011))) ≤ 0.000565303203 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001327149674 / (13192 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565303203 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565303203 : ℝ) + 3.141593 * 0.052289576707 / (13192 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001143197345 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052289576707)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327149674) : PiBarMP 13192 12 0.011 xi bn ≤ 0.158185970086 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13192 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036430065523 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.222974921860 : ℝ) ≤ √((13192 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.856432122889 : ℝ) ≤ √(13192 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13192) ≤ 0.121302812610 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036430065523 + 0.052289576707 * 1.772454 / (2 * (114.222974921860 : ℝ))) * (1 + 0.001143197345) +
        8 / (13192 * 114.856432122889) + 0.121302812610 := by gcongr
    _ ≤ (0.158185970086 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052289576707)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327149674) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280154934016) :
    parallelOracle 13192 0.011 xi bn cd ≤ 0.159139710047 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13192 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13192 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560524988182 : ℝ) ≤ plow 13192 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.856432122889 : ℝ) ≤ √(13192 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280154934016 : ℝ) / (2 * 0.560524988182 * 114.856432122889)) * 0.158185970086 +
        0.280154934016 ^ 2 / (2 * 0.560524988182 * 114.856432122889) := by gcongr
    _ ≤ (0.159139710047 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052289576707) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327149674)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280154934016) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13192 13192 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560524988182 : ℝ) ≤ plow 13192 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.856432122889 : ℝ) ≤ √(13192 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13192 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13192 Θ 1.22 ≤ 0.011545722565 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.856432122889 := by gcongr <;> linarith
      _ ≤ (0.011545722565 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13192 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13192 13192 0.011 ≤ 0.008322449813 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13192 13192 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13192 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13192 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13192 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13192 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159139710047 + 0.011545722565 + (0.008322449813 : ℝ) *
        (1 + 2 * (0.280154934016 + 0.011545722565) / (0.560524988182 * 114.856432122889))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13192]

end BstLean.Part269.N13192

/-! The original eight local profiles supply actual 13192 moment certificates. -/
namespace BstLean.Part269.N13192
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13192 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13192 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13192 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052289576707 ∧
    0 ≤ bN 13192 BstLean.Part154.csC (groupTheta g) ∧ bN 13192 BstLean.Part154.csC (groupTheta g) ≤ 0.001327149674 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13192 13192 0.011
      (momentAllowance 13192 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13192 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13192 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13192 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13192 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13192 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228669142447 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13192 0.011
      (momentAllowance 13192 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13192 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13192
/-! The actual computed-centre upper energy formula at 13192. -/
namespace BstLean.Part269.N13192
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13192

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13192
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13192)
open BstLean.Part268 (cell13192)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084171396520
  | 2 => 0.085093919113
  | 3 => 0.086011757928
  | 4 => 0.086925665386
  | 5 => 0.087836570137
  | 6 => 0.088745605468
  | 7 => 0.089654140816
  | 8 => 0.090563816512
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13192 13192 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13192 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13192

/-! Actual upper energy certificates on all 43 source endpoints at 13192. -/
namespace BstLean.Part269.N13192
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13192)
open BstLean.Part268 (cell13192)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13192 (gMinus 13192) (1 - (cell13192 i).lower) ≤ 1 ∧
    energyUpper 13192 (gMinus 13192) (BstLean.Part211.gPlus 13192)
      (finiteEnergy 13192 13192 0.011) (1 - (cell13192 i).lower) ≤
      (cell13192 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨10,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨11,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨12,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨13,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨14,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨15,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨16,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨17,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨18,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨19,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨20,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨21,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨22,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨23,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨24,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨25,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨26,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨27,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨28,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨29,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨30,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨31,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨32,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨33,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨34,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨35,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨36,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨37,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨38,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨39,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨40,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨41,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨42,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨43,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨44,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨45,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨46,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨47,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨48,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨49,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨50,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨51,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13192) (by norm_num)
        (q := 1 - (cell13192 ⟨52,by decide⟩).lower)
        (by norm_num [cell13192]) (by norm_num [cell13192])
      exact ⟨E.1,E.2.trans (by norm_num [cell13192])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13192

/-! Source-cell containment and simple scalar guards at 13192. -/
namespace BstLean.Part269.N13192
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13192)
open BstLean.Part268 (cell13192)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13192 ⟨10,by decide⟩).lower ∧ (cell13192 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13192 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13192 ⟨11,by decide⟩).lower ∧ (cell13192 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13192 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13192 ⟨12,by decide⟩).lower ∧ (cell13192 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13192 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13192 ⟨13,by decide⟩).lower ∧ (cell13192 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13192 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13192 ⟨14,by decide⟩).lower ∧ (cell13192 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13192 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13192 ⟨15,by decide⟩).lower ∧ (cell13192 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13192 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13192 ⟨16,by decide⟩).lower ∧ (cell13192 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13192 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13192 ⟨17,by decide⟩).lower ∧ (cell13192 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13192 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13192 ⟨18,by decide⟩).lower ∧ (cell13192 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13192 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13192 ⟨19,by decide⟩).lower ∧ (cell13192 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13192 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13192 ⟨20,by decide⟩).lower ∧ (cell13192 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13192 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13192 ⟨21,by decide⟩).lower ∧ (cell13192 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13192 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13192 ⟨22,by decide⟩).lower ∧ (cell13192 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13192 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13192 ⟨23,by decide⟩).lower ∧ (cell13192 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13192 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13192 ⟨24,by decide⟩).lower ∧ (cell13192 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13192 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13192 ⟨25,by decide⟩).lower ∧ (cell13192 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13192 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13192 ⟨26,by decide⟩).lower ∧ (cell13192 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13192 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13192 ⟨27,by decide⟩).lower ∧ (cell13192 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13192 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13192 ⟨28,by decide⟩).lower ∧ (cell13192 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13192 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13192 ⟨29,by decide⟩).lower ∧ (cell13192 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13192 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13192 ⟨30,by decide⟩).lower ∧ (cell13192 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13192 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13192 ⟨31,by decide⟩).lower ∧ (cell13192 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13192 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13192 ⟨32,by decide⟩).lower ∧ (cell13192 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13192 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13192 ⟨33,by decide⟩).lower ∧ (cell13192 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13192 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13192 ⟨34,by decide⟩).lower ∧ (cell13192 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13192 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13192 ⟨35,by decide⟩).lower ∧ (cell13192 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13192 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13192 ⟨36,by decide⟩).lower ∧ (cell13192 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13192 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13192 ⟨37,by decide⟩).lower ∧ (cell13192 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13192 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13192 ⟨38,by decide⟩).lower ∧ (cell13192 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13192 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13192 ⟨39,by decide⟩).lower ∧ (cell13192 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13192 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13192 ⟨40,by decide⟩).lower ∧ (cell13192 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13192 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13192 ⟨41,by decide⟩).lower ∧ (cell13192 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13192 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13192 ⟨42,by decide⟩).lower ∧ (cell13192 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13192 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13192 ⟨43,by decide⟩).lower ∧ (cell13192 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13192 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13192 ⟨44,by decide⟩).lower ∧ (cell13192 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13192 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13192 ⟨45,by decide⟩).lower ∧ (cell13192 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13192 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13192 ⟨46,by decide⟩).lower ∧ (cell13192 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13192 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13192 ⟨47,by decide⟩).lower ∧ (cell13192 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13192 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13192 ⟨48,by decide⟩).lower ∧ (cell13192 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13192 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13192 ⟨49,by decide⟩).lower ∧ (cell13192 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13192 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13192 ⟨50,by decide⟩).lower ∧ (cell13192 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13192 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13192 ⟨51,by decide⟩).lower ∧ (cell13192 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13192 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13192 ⟨52,by decide⟩).lower ∧ (cell13192 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13192 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13192 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13192 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13192,cell13192,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13192 i).lower ∧
    (cell13192 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13192 i).upper ≤ (0.532 : ℝ) ∧
    (cell13192 i).centre ≤ (0.1 : ℝ) ∧ (cell13192 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13192 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13192 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13192

/-! The local source numeric instances at 13192 have no network premises. -/
namespace BstLean.Part269.N13192
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13192)
open BstLean.Part268 (cell13192)

noncomputable def sourceNumerics13192 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13192 (cell13192 i)
      scalarRow13192.M scalarRow13192.H scalarRow13192.xi := by
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
    energy_allowance := scalarRow13192.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13192]
    centre_nonneg := (scalarRow13192.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13192])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13192
/-! Actual 13193 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13193
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13193 ≤ (1.035127957342 : ℝ) := by
  have hr : (114.860785301163 : ℝ) ≤ √(13193 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.860785301163 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13193 13193 (11 / 1000) ≤
    (0.008322134393 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13193) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.860785301163 : ℝ) ≤ √(13193 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13193)
  have hdiv : K / √(13193 : ℝ) ≤ K / 114.860785301163 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.860785301163 ≤ (0.008322134393 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13193.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13193 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13193 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13193 := gPlus_lower 13193
end BstLean.Part269.N13193

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13193
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035127957341 : ℝ) ≤ wn 13193 := by
  have hn : √(13193 : ℝ) ≤ 114.860785301164 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13193 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.860785301164 ≤ 2 / √(13193 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242309034 : ℝ) ≤ rhoBar 13193 BstLean.Part154.csC ∧
    rhoBar 13193 BstLean.Part154.csC ≤ 0.000242309410 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035127957341 : ℝ) / (1.295212 * 13193) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035127957342 : ℝ) / (1.29521 * 13193) := by gcongr
      _ ≤ (0.000242309410 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13193 BstLean.Part154.csC) ≤ 0.000969296354 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13193 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13193 BstLean.Part154.csC) (piBar (rhoBar 13193 BstLean.Part154.csC)) ≤ 0.000185077235 ∧
    cc1 (rhoBar 13193 BstLean.Part154.csC) (piBar (rhoBar 13193 BstLean.Part154.csC)) ≤ 0.000117765941 ∧
    cc2 (rhoBar 13193 BstLean.Part154.csC) ≤ 0.000068364113 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13193 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13193 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13193 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13193 BstLean.Part154.csC * nuR (rhoBar 13193 BstLean.Part154.csC)) ≤ 0.000484633499 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242309410 : ℝ) * 0.000969296354 := by gcongr
      _ ≤ (0.000484633499 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13193 BstLean.Part154.csC) * nuR (rhoBar 13193 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000969296354 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13193 BstLean.Part154.csC) * rhoBar 13193 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242309410 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242309410 / 2 + 0.399 * 0.000969296354 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185077235 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484633499 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117765941 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242309410 / 1.414213562 := by gcongr
      _ ≤ (0.000068364113 : ℝ) := by norm_num

end BstLean.Part269.N13193

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13193
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13193 BstLean.Part154.csC) (piBar (rhoBar 13193 BstLean.Part154.csC)) ≤ 1.47925E-7 := by
  have hr0 : 0 ≤ rhoBar 13193 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13193 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13193 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13193 BstLean.Part154.csC) (piBar (rhoBar 13193 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13193 BstLean.Part154.csC) (piBar (rhoBar 13193 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13193 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185077235 : ℝ) ^ 2 + 0.000117765941 ^ 2 + 3 * 0.000068364113 ^ 2 +
        2 * 0.797885 * 0.000185077235 * 0.000117765941 + 2 * 0.000185077235 * 0.000068364113 +
        4 * 0.797885 * 0.000117765941 * 0.000068364113 := by gcongr
    _ ≤ (1.47925E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13193 BstLean.Part154.csC Θ ≤ 0.002527702754 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13193 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13193 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13193 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13193 BstLean.Part154.csC) (piBar (rhoBar 13193 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13193 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035127957342 * 1.47925E-7 / (0.000242309034 : ℝ) := by gcongr
    _ ≤ 0.002527702754 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13193 BstLean.Part154.csC Θ ≤ 0.002802777795 + 0.000638711188 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13193 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13193 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13193 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035127957342 : ℝ) * ((2 * Θ * 0.000242309410 +
        (6863 / 10000) * 0.000242309410 * 13193 * 0.000969296354) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002802777795 + 0.000638711188 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13193 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13193 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13193 0.011 Θ ∧ gammaRatio 13193 0.011 Θ ≤ 0.000083299709 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13193 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035127957342 : ℝ) * 0.525 / ((1 - 0.011) * 13193) := by gcongr
      _ ≤ (0.000083299709 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13193 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13193 0.011 Θ) :=
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
    badAllowance 13193 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13193 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13193 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13193 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13193 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13193 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13193 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13193 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13193 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13193 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13193 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035127957342 : ℝ) * 13193 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13193 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003120253995 + 0.003166413942 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13193

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13193
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13193 BstLean.Part154.csC) (piBar (rhoBar 13193 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13193 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13193 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13193 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13193 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13193 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13193 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13193 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13193 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13193 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13193 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13193 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13193 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13193 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13193 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051483819514 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13193) ≤ 0.010397261154 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13193 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035127957342)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010397261154 + 2 * 0.737676 / 13193) := by gcongr
    _ ≤ (0.051483819514 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13193 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13193

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13193
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525030091 : ℝ) ≤ plow 13193 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13193) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052289221315)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327043946) : eMP 13193 0.011 xi bn ≤ 0.001143108421 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13193 : ℝ) * (1 - 0.011))) ≤ 0.000565259261 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001327043946 / (13193 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565259261 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565259261 : ℝ) + 3.141593 * 0.052289221315 / (13193 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001143108421 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052289221315)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327043946) : PiBarMP 13193 12 0.011 xi bn ≤ 0.158179897930 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13193 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036428614385 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.227304091447 : ℝ) ≤ √((13193 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.860785301163 : ℝ) ≤ √(13193 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13193) ≤ 0.121298215281 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036428614385 + 0.052289221315 * 1.772454 / (2 * (114.227304091447 : ℝ))) * (1 + 0.001143108421) +
        8 / (13193 * 114.860785301163) + 0.121298215281 := by gcongr
    _ ≤ (0.158179897930 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052289221315)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327043946) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280152184871) :
    parallelOracle 13193 0.011 xi bn cd ≤ 0.159133573122 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13193 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13193 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525030091 : ℝ) ≤ plow 13193 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.860785301163 : ℝ) ≤ √(13193 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280152184871 : ℝ) / (2 * 0.560525030091 * 114.860785301163)) * 0.158179897930 +
        0.280152184871 ^ 2 / (2 * 0.560525030091 * 114.860785301163) := by gcongr
    _ ≤ (0.159133573122 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052289221315) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001327043946)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280152184871) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13193 13193 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525030091 : ℝ) ≤ plow 13193 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.860785301163 : ℝ) ≤ √(13193 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13193 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13193 Θ 1.22 ≤ 0.011545284986 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.860785301163 := by gcongr <;> linarith
      _ ≤ (0.011545284986 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13193 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13193 13193 0.011 ≤ 0.008322134393 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13193 13193 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13193 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13193 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13193 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13193 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159133573122 + 0.011545284986 + (0.008322134393 : ℝ) *
        (1 + 2 * (0.280152184871 + 0.011545284986) / (0.560525030091 * 114.860785301163))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13193]

end BstLean.Part269.N13193

/-! The original eight local profiles supply actual 13193 moment certificates. -/
namespace BstLean.Part269.N13193
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13193 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13193 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13193 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052289221315 ∧
    0 ≤ bN 13193 BstLean.Part154.csC (groupTheta g) ∧ bN 13193 BstLean.Part154.csC (groupTheta g) ≤ 0.001327043946 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13193 13193 0.011
      (momentAllowance 13193 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13193 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13193 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13193 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13193 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13193 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228668365357 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13193 0.011
      (momentAllowance 13193 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13193 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13193
/-! The actual computed-centre upper energy formula at 13193. -/
namespace BstLean.Part269.N13193
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13193

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13193
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13193)
open BstLean.Part268 (cell13193)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084168920592
  | 2 => 0.085091413488
  | 3 => 0.086009218521
  | 4 => 0.086923087127
  | 5 => 0.087833946787
  | 6 => 0.088742929407
  | 7 => 0.089651402809
  | 8 => 0.090561005438
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13193 13193 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13193 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13193

/-! Actual upper energy certificates on all 43 source endpoints at 13193. -/
namespace BstLean.Part269.N13193
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13193)
open BstLean.Part268 (cell13193)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13193 (gMinus 13193) (1 - (cell13193 i).lower) ≤ 1 ∧
    energyUpper 13193 (gMinus 13193) (BstLean.Part211.gPlus 13193)
      (finiteEnergy 13193 13193 0.011) (1 - (cell13193 i).lower) ≤
      (cell13193 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨10,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨11,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨12,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨13,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨14,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨15,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨16,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨17,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨18,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨19,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨20,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨21,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨22,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨23,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨24,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨25,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨26,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨27,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨28,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨29,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨30,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨31,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨32,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨33,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨34,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨35,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨36,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨37,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨38,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨39,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨40,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨41,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨42,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨43,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨44,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨45,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨46,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨47,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨48,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨49,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨50,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨51,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13193) (by norm_num)
        (q := 1 - (cell13193 ⟨52,by decide⟩).lower)
        (by norm_num [cell13193]) (by norm_num [cell13193])
      exact ⟨E.1,E.2.trans (by norm_num [cell13193])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13193

/-! Source-cell containment and simple scalar guards at 13193. -/
namespace BstLean.Part269.N13193
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13193)
open BstLean.Part268 (cell13193)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13193 ⟨10,by decide⟩).lower ∧ (cell13193 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13193 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13193 ⟨11,by decide⟩).lower ∧ (cell13193 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13193 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13193 ⟨12,by decide⟩).lower ∧ (cell13193 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13193 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13193 ⟨13,by decide⟩).lower ∧ (cell13193 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13193 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13193 ⟨14,by decide⟩).lower ∧ (cell13193 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13193 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13193 ⟨15,by decide⟩).lower ∧ (cell13193 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13193 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13193 ⟨16,by decide⟩).lower ∧ (cell13193 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13193 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13193 ⟨17,by decide⟩).lower ∧ (cell13193 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13193 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13193 ⟨18,by decide⟩).lower ∧ (cell13193 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13193 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13193 ⟨19,by decide⟩).lower ∧ (cell13193 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13193 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13193 ⟨20,by decide⟩).lower ∧ (cell13193 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13193 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13193 ⟨21,by decide⟩).lower ∧ (cell13193 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13193 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13193 ⟨22,by decide⟩).lower ∧ (cell13193 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13193 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13193 ⟨23,by decide⟩).lower ∧ (cell13193 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13193 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13193 ⟨24,by decide⟩).lower ∧ (cell13193 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13193 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13193 ⟨25,by decide⟩).lower ∧ (cell13193 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13193 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13193 ⟨26,by decide⟩).lower ∧ (cell13193 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13193 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13193 ⟨27,by decide⟩).lower ∧ (cell13193 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13193 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13193 ⟨28,by decide⟩).lower ∧ (cell13193 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13193 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13193 ⟨29,by decide⟩).lower ∧ (cell13193 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13193 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13193 ⟨30,by decide⟩).lower ∧ (cell13193 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13193 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13193 ⟨31,by decide⟩).lower ∧ (cell13193 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13193 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13193 ⟨32,by decide⟩).lower ∧ (cell13193 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13193 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13193 ⟨33,by decide⟩).lower ∧ (cell13193 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13193 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13193 ⟨34,by decide⟩).lower ∧ (cell13193 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13193 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13193 ⟨35,by decide⟩).lower ∧ (cell13193 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13193 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13193 ⟨36,by decide⟩).lower ∧ (cell13193 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13193 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13193 ⟨37,by decide⟩).lower ∧ (cell13193 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13193 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13193 ⟨38,by decide⟩).lower ∧ (cell13193 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13193 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13193 ⟨39,by decide⟩).lower ∧ (cell13193 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13193 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13193 ⟨40,by decide⟩).lower ∧ (cell13193 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13193 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13193 ⟨41,by decide⟩).lower ∧ (cell13193 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13193 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13193 ⟨42,by decide⟩).lower ∧ (cell13193 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13193 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13193 ⟨43,by decide⟩).lower ∧ (cell13193 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13193 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13193 ⟨44,by decide⟩).lower ∧ (cell13193 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13193 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13193 ⟨45,by decide⟩).lower ∧ (cell13193 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13193 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13193 ⟨46,by decide⟩).lower ∧ (cell13193 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13193 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13193 ⟨47,by decide⟩).lower ∧ (cell13193 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13193 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13193 ⟨48,by decide⟩).lower ∧ (cell13193 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13193 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13193 ⟨49,by decide⟩).lower ∧ (cell13193 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13193 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13193 ⟨50,by decide⟩).lower ∧ (cell13193 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13193 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13193 ⟨51,by decide⟩).lower ∧ (cell13193 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13193 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13193 ⟨52,by decide⟩).lower ∧ (cell13193 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13193 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13193 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13193 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13193,cell13193,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13193 i).lower ∧
    (cell13193 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13193 i).upper ≤ (0.532 : ℝ) ∧
    (cell13193 i).centre ≤ (0.1 : ℝ) ∧ (cell13193 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13193 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13193 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13193

/-! The local source numeric instances at 13193 have no network premises. -/
namespace BstLean.Part269.N13193
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13193)
open BstLean.Part268 (cell13193)

noncomputable def sourceNumerics13193 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13193 (cell13193 i)
      scalarRow13193.M scalarRow13193.H scalarRow13193.xi := by
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
    energy_allowance := scalarRow13193.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13193]
    centre_nonneg := (scalarRow13193.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13193])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13193
/-! Actual 13194 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13194
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13194 ≤ (1.035126614618 : ℝ) := by
  have hr : (114.865138314459 : ℝ) ≤ √(13194 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.865138314459 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13194 13194 (11 / 1000) ≤
    (0.008321819009 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13194) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.865138314459 : ℝ) ≤ √(13194 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13194)
  have hdiv : K / √(13194 : ℝ) ≤ K / 114.865138314459 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.865138314459 ≤ (0.008321819009 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13194.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13194 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13194 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13194 := gPlus_lower 13194
end BstLean.Part269.N13194

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13194
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035126614617 : ℝ) ≤ wn 13194 := by
  have hn : √(13194 : ℝ) ≤ 114.865138314460 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13194 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.865138314460 ≤ 2 / √(13194 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242290355 : ℝ) ≤ rhoBar 13194 BstLean.Part154.csC ∧
    rhoBar 13194 BstLean.Part154.csC ≤ 0.000242290730 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035126614617 : ℝ) / (1.295212 * 13194) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035126614618 : ℝ) / (1.29521 * 13194) := by gcongr
      _ ≤ (0.000242290730 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13194 BstLean.Part154.csC) ≤ 0.000969221625 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13194 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13194 BstLean.Part154.csC) (piBar (rhoBar 13194 BstLean.Part154.csC)) ≤ 0.000185062966 ∧
    cc1 (rhoBar 13194 BstLean.Part154.csC) (piBar (rhoBar 13194 BstLean.Part154.csC)) ≤ 0.000117756862 ∧
    cc2 (rhoBar 13194 BstLean.Part154.csC) ≤ 0.000068358842 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13194 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13194 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13194 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13194 BstLean.Part154.csC * nuR (rhoBar 13194 BstLean.Part154.csC)) ≤ 0.000484596137 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242290730 : ℝ) * 0.000969221625 := by gcongr
      _ ≤ (0.000484596137 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13194 BstLean.Part154.csC) * nuR (rhoBar 13194 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000969221625 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13194 BstLean.Part154.csC) * rhoBar 13194 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242290730 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242290730 / 2 + 0.399 * 0.000969221625 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185062966 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484596137 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117756862 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242290730 / 1.414213562 := by gcongr
      _ ≤ (0.000068358842 : ℝ) := by norm_num

end BstLean.Part269.N13194

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13194
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13194 BstLean.Part154.csC) (piBar (rhoBar 13194 BstLean.Part154.csC)) ≤ 1.47902E-7 := by
  have hr0 : 0 ≤ rhoBar 13194 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13194 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13194 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13194 BstLean.Part154.csC) (piBar (rhoBar 13194 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13194 BstLean.Part154.csC) (piBar (rhoBar 13194 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13194 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185062966 : ℝ) ^ 2 + 0.000117756862 ^ 2 + 3 * 0.000068358842 ^ 2 +
        2 * 0.797885 * 0.000185062966 * 0.000117756862 + 2 * 0.000185062966 * 0.000068358842 +
        4 * 0.797885 * 0.000117756862 * 0.000068358842 := by gcongr
    _ ≤ (1.47902E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13194 BstLean.Part154.csC Θ ≤ 0.002527501296 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13194 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13194 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13194 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13194 BstLean.Part154.csC) (piBar (rhoBar 13194 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13194 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035126614618 * 1.47902E-7 / (0.000242290355 : ℝ) := by gcongr
    _ ≤ 0.002527501296 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13194 BstLean.Part154.csC Θ ≤ 0.002802554434 + 0.000638661120 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13194 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13194 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13194 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035126614618 : ℝ) * ((2 * Θ * 0.000242290730 +
        (6863 / 10000) * 0.000242290730 * 13194 * 0.000969221625) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002802554434 + 0.000638661120 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13194 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13194 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13194 0.011 Θ ∧ gammaRatio 13194 0.011 Θ ≤ 0.000083293288 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13194 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035126614618 : ℝ) * 0.525 / ((1 - 0.011) * 13194) := by gcongr
      _ ≤ (0.000083293288 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13194 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13194 0.011 Θ) :=
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
    badAllowance 13194 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13194 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13194 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13194 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13194 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13194 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13194 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13194 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13194 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13194 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13194 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035126614618 : ℝ) * 13194 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13194 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003120030634 + 0.003166162416 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13194

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13194
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13194 BstLean.Part154.csC) (piBar (rhoBar 13194 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13194 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13194 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13194 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13194 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13194 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13194 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13194 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13194 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13194 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13194 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13194 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13194 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13194 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13194 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051481847685 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13194) ≤ 0.010396867132 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13194 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035126614618)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010396867132 + 2 * 0.737676 / 13194) := by gcongr
    _ ≤ (0.051481847685 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13194 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13194

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13194
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525071994 : ℝ) ≤ plow 13194 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13194) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052288865903)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326938181) : eMP 13194 0.011 xi bn ≤ 0.001143019488 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13194 : ℝ) * (1 - 0.011))) ≤ 0.000565215314 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001326938181 / (13194 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565215314 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565215314 : ℝ) + 3.141593 * 0.052288865903 / (13194 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001143019488 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052288865903)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326938181) : PiBarMP 13194 12 0.011 xi bn ≤ 0.158173825733 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13194 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036427162682 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.231633096966 : ℝ) ≤ √((13194 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.865138314459 : ℝ) ≤ √(13194 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13194) ≤ 0.121293618475 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036427162682 + 0.052288865903 * 1.772454 / (2 * (114.231633096966 : ℝ))) * (1 + 0.001143019488) +
        8 / (13194 * 114.865138314459) + 0.121293618475 := by gcongr
    _ ≤ (0.158173825733 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052288865903)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326938181) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280149435907) :
    parallelOracle 13194 0.011 xi bn cd ≤ 0.159127436164 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13194 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13194 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525071994 : ℝ) ≤ plow 13194 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.865138314459 : ℝ) ≤ √(13194 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280149435907 : ℝ) / (2 * 0.560525071994 * 114.865138314459)) * 0.158173825733 +
        0.280149435907 ^ 2 / (2 * 0.560525071994 * 114.865138314459) := by gcongr
    _ ≤ (0.159127436164 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052288865903) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326938181)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280149435907) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13194 13194 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525071994 : ℝ) ≤ plow 13194 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.865138314459 : ℝ) ≤ √(13194 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13194 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13194 Θ 1.22 ≤ 0.011544847458 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.865138314459 := by gcongr <;> linarith
      _ ≤ (0.011544847458 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13194 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13194 13194 0.011 ≤ 0.008321819009 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13194 13194 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13194 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13194 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13194 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13194 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159127436164 + 0.011544847458 + (0.008321819009 : ℝ) *
        (1 + 2 * (0.280149435907 + 0.011544847458) / (0.560525071994 * 114.865138314459))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13194]

end BstLean.Part269.N13194

/-! The original eight local profiles supply actual 13194 moment certificates. -/
namespace BstLean.Part269.N13194
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13194 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13194 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13194 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052288865903 ∧
    0 ≤ bN 13194 BstLean.Part154.csC (groupTheta g) ∧ bN 13194 BstLean.Part154.csC (groupTheta g) ≤ 0.001326938181 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13194 13194 0.011
      (momentAllowance 13194 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13194 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13194 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13194 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13194 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13194 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228667588222 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13194 0.011
      (momentAllowance 13194 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13194 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13194
/-! The actual computed-centre upper energy formula at 13194. -/
namespace BstLean.Part269.N13194
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13194

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13194
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13194)
open BstLean.Part268 (cell13194)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084166445343
  | 2 => 0.085088908565
  | 3 => 0.086006679843
  | 4 => 0.086920509632
  | 5 => 0.087831324243
  | 6 => 0.088740254204
  | 7 => 0.089648665722
  | 8 => 0.090558195361
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13194 13194 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13194 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13194

/-! Actual upper energy certificates on all 43 source endpoints at 13194. -/
namespace BstLean.Part269.N13194
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13194)
open BstLean.Part268 (cell13194)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13194 (gMinus 13194) (1 - (cell13194 i).lower) ≤ 1 ∧
    energyUpper 13194 (gMinus 13194) (BstLean.Part211.gPlus 13194)
      (finiteEnergy 13194 13194 0.011) (1 - (cell13194 i).lower) ≤
      (cell13194 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨10,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨11,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨12,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨13,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨14,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨15,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨16,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨17,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨18,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨19,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨20,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨21,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨22,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨23,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨24,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨25,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨26,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨27,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨28,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨29,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨30,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨31,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨32,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨33,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨34,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨35,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨36,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨37,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨38,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨39,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨40,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨41,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨42,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨43,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨44,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨45,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨46,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨47,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨48,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨49,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨50,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨51,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13194) (by norm_num)
        (q := 1 - (cell13194 ⟨52,by decide⟩).lower)
        (by norm_num [cell13194]) (by norm_num [cell13194])
      exact ⟨E.1,E.2.trans (by norm_num [cell13194])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13194

/-! Source-cell containment and simple scalar guards at 13194. -/
namespace BstLean.Part269.N13194
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13194)
open BstLean.Part268 (cell13194)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13194 ⟨10,by decide⟩).lower ∧ (cell13194 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13194 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13194 ⟨11,by decide⟩).lower ∧ (cell13194 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13194 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13194 ⟨12,by decide⟩).lower ∧ (cell13194 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13194 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13194 ⟨13,by decide⟩).lower ∧ (cell13194 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13194 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13194 ⟨14,by decide⟩).lower ∧ (cell13194 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13194 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13194 ⟨15,by decide⟩).lower ∧ (cell13194 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13194 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13194 ⟨16,by decide⟩).lower ∧ (cell13194 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13194 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13194 ⟨17,by decide⟩).lower ∧ (cell13194 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13194 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13194 ⟨18,by decide⟩).lower ∧ (cell13194 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13194 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13194 ⟨19,by decide⟩).lower ∧ (cell13194 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13194 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13194 ⟨20,by decide⟩).lower ∧ (cell13194 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13194 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13194 ⟨21,by decide⟩).lower ∧ (cell13194 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13194 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13194 ⟨22,by decide⟩).lower ∧ (cell13194 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13194 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13194 ⟨23,by decide⟩).lower ∧ (cell13194 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13194 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13194 ⟨24,by decide⟩).lower ∧ (cell13194 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13194 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13194 ⟨25,by decide⟩).lower ∧ (cell13194 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13194 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13194 ⟨26,by decide⟩).lower ∧ (cell13194 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13194 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13194 ⟨27,by decide⟩).lower ∧ (cell13194 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13194 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13194 ⟨28,by decide⟩).lower ∧ (cell13194 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13194 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13194 ⟨29,by decide⟩).lower ∧ (cell13194 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13194 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13194 ⟨30,by decide⟩).lower ∧ (cell13194 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13194 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13194 ⟨31,by decide⟩).lower ∧ (cell13194 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13194 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13194 ⟨32,by decide⟩).lower ∧ (cell13194 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13194 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13194 ⟨33,by decide⟩).lower ∧ (cell13194 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13194 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13194 ⟨34,by decide⟩).lower ∧ (cell13194 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13194 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13194 ⟨35,by decide⟩).lower ∧ (cell13194 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13194 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13194 ⟨36,by decide⟩).lower ∧ (cell13194 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13194 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13194 ⟨37,by decide⟩).lower ∧ (cell13194 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13194 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13194 ⟨38,by decide⟩).lower ∧ (cell13194 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13194 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13194 ⟨39,by decide⟩).lower ∧ (cell13194 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13194 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13194 ⟨40,by decide⟩).lower ∧ (cell13194 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13194 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13194 ⟨41,by decide⟩).lower ∧ (cell13194 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13194 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13194 ⟨42,by decide⟩).lower ∧ (cell13194 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13194 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13194 ⟨43,by decide⟩).lower ∧ (cell13194 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13194 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13194 ⟨44,by decide⟩).lower ∧ (cell13194 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13194 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13194 ⟨45,by decide⟩).lower ∧ (cell13194 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13194 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13194 ⟨46,by decide⟩).lower ∧ (cell13194 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13194 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13194 ⟨47,by decide⟩).lower ∧ (cell13194 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13194 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13194 ⟨48,by decide⟩).lower ∧ (cell13194 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13194 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13194 ⟨49,by decide⟩).lower ∧ (cell13194 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13194 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13194 ⟨50,by decide⟩).lower ∧ (cell13194 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13194 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13194 ⟨51,by decide⟩).lower ∧ (cell13194 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13194 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13194 ⟨52,by decide⟩).lower ∧ (cell13194 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13194 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13194 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13194 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13194,cell13194,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13194 i).lower ∧
    (cell13194 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13194 i).upper ≤ (0.532 : ℝ) ∧
    (cell13194 i).centre ≤ (0.1 : ℝ) ∧ (cell13194 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13194 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13194 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13194

/-! The local source numeric instances at 13194 have no network premises. -/
namespace BstLean.Part269.N13194
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13194)
open BstLean.Part268 (cell13194)

noncomputable def sourceNumerics13194 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13194 (cell13194 i)
      scalarRow13194.M scalarRow13194.H scalarRow13194.xi := by
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
    energy_allowance := scalarRow13194.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13194]
    centre_nonneg := (scalarRow13194.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13194])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13194
/-! Actual 13195 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13195
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13195 ≤ (1.035125272047 : ℝ) := by
  have hr : (114.869491162797 : ℝ) ≤ √(13195 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.869491162797 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13195 13195 (11 / 1000) ≤
    (0.008321503661 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13195) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.869491162797 : ℝ) ≤ √(13195 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13195)
  have hdiv : K / √(13195 : ℝ) ≤ K / 114.869491162797 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.869491162797 ≤ (0.008321503661 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13195.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13195 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13195 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13195 := gPlus_lower 13195
end BstLean.Part269.N13195

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13195
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035125272046 : ℝ) ≤ wn 13195 := by
  have hn : √(13195 : ℝ) ≤ 114.869491162798 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13195 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.869491162798 ≤ 2 / √(13195 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242271679 : ℝ) ≤ rhoBar 13195 BstLean.Part154.csC ∧
    rhoBar 13195 BstLean.Part154.csC ≤ 0.000242272054 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035125272046 : ℝ) / (1.295212 * 13195) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035125272047 : ℝ) / (1.29521 * 13195) := by gcongr
      _ ≤ (0.000242272054 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13195 BstLean.Part154.csC) ≤ 0.000969146912 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13195 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13195 BstLean.Part154.csC) (piBar (rhoBar 13195 BstLean.Part154.csC)) ≤ 0.000185048701 ∧
    cc1 (rhoBar 13195 BstLean.Part154.csC) (piBar (rhoBar 13195 BstLean.Part154.csC)) ≤ 0.000117747785 ∧
    cc2 (rhoBar 13195 BstLean.Part154.csC) ≤ 0.000068353573 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13195 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13195 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13195 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13195 BstLean.Part154.csC * nuR (rhoBar 13195 BstLean.Part154.csC)) ≤ 0.000484558782 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242272054 : ℝ) * 0.000969146912 := by gcongr
      _ ≤ (0.000484558782 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13195 BstLean.Part154.csC) * nuR (rhoBar 13195 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000969146912 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13195 BstLean.Part154.csC) * rhoBar 13195 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242272054 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242272054 / 2 + 0.399 * 0.000969146912 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185048701 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484558782 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117747785 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242272054 / 1.414213562 := by gcongr
      _ ≤ (0.000068353573 : ℝ) := by norm_num

end BstLean.Part269.N13195

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13195
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13195 BstLean.Part154.csC) (piBar (rhoBar 13195 BstLean.Part154.csC)) ≤ 1.47880E-7 := by
  have hr0 : 0 ≤ rhoBar 13195 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13195 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13195 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13195 BstLean.Part154.csC) (piBar (rhoBar 13195 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13195 BstLean.Part154.csC) (piBar (rhoBar 13195 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13195 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185048701 : ℝ) ^ 2 + 0.000117747785 ^ 2 + 3 * 0.000068353573 ^ 2 +
        2 * 0.797885 * 0.000185048701 * 0.000117747785 + 2 * 0.000185048701 * 0.000068353573 +
        4 * 0.797885 * 0.000117747785 * 0.000068353573 := by gcongr
    _ ≤ (1.47880E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13195 BstLean.Part154.csC Θ ≤ 0.002527316868 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13195 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13195 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13195 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13195 BstLean.Part154.csC) (piBar (rhoBar 13195 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13195 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035125272047 * 1.47880E-7 / (0.000242271679 : ℝ) := by gcongr
    _ ≤ 0.002527316868 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13195 BstLean.Part154.csC Θ ≤ 0.002802331134 + 0.000638611063 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13195 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13195 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13195 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035125272047 : ℝ) * ((2 * Θ * 0.000242272054 +
        (6863 / 10000) * 0.000242272054 * 13195 * 0.000969146912) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002802331134 + 0.000638611063 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13195 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13195 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13195 0.011 Θ ∧ gammaRatio 13195 0.011 Θ ≤ 0.000083286867 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13195 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035125272047 : ℝ) * 0.525 / ((1 - 0.011) * 13195) := by gcongr
      _ ≤ (0.000083286867 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13195 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13195 0.011 Θ) :=
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
    badAllowance 13195 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13195 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13195 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13195 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13195 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13195 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13195 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13195 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13195 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13195 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13195 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035125272047 : ℝ) * 13195 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13195 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003119807334 + 0.003165927931 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13195

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13195
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13195 BstLean.Part154.csC) (piBar (rhoBar 13195 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13195 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13195 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13195 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13195 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13195 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13195 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13195 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13195 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13195 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13195 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13195 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13195 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13195 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13195 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051479876079 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13195) ≤ 0.010396473154 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13195 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035125272047)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010396473154 + 2 * 0.737676 / 13195) := by gcongr
    _ ≤ (0.051479876079 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13195 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13195

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13195
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525113891 : ℝ) ≤ plow 13195 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13195) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052288519498)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326841356) : eMP 13195 0.011 xi bn ≤ 0.001142934372 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13195 : ℝ) * (1 - 0.011))) ≤ 0.000565173275 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001326841356 / (13195 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565173275 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565173275 : ℝ) + 3.141593 * 0.052288519498 / (13195 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001142934372 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052288519498)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326841356) : PiBarMP 13195 12 0.011 xi bn ≤ 0.158167877069 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13195 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036425833635 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.235961938436 : ℝ) ≤ √((13195 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.869491162797 : ℝ) ≤ √(13195 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13195) ≤ 0.121289022192 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036425833635 + 0.052288519498 * 1.772454 / (2 * (114.235961938436 : ℝ))) * (1 + 0.001142934372) +
        8 / (13195 * 114.869491162797) + 0.121289022192 := by gcongr
    _ ≤ (0.158167877069 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052288519498)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326841356) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280146706857) :
    parallelOracle 13195 0.011 xi bn cd ≤ 0.159121423126 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13195 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13195 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525113891 : ℝ) ≤ plow 13195 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.869491162797 : ℝ) ≤ √(13195 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280146706857 : ℝ) / (2 * 0.560525113891 * 114.869491162797)) * 0.158167877069 +
        0.280146706857 ^ 2 / (2 * 0.560525113891 * 114.869491162797) := by gcongr
    _ ≤ (0.159121423126 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052288519498) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326841356)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280146706857) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13195 13195 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525113891 : ℝ) ≤ plow 13195 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.869491162797 : ℝ) ≤ √(13195 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13195 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13195 Θ 1.22 ≤ 0.011544409979 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.869491162797 := by gcongr <;> linarith
      _ ≤ (0.011544409979 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13195 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13195 13195 0.011 ≤ 0.008321503661 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13195 13195 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13195 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13195 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13195 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13195 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159121423126 + 0.011544409979 + (0.008321503661 : ℝ) *
        (1 + 2 * (0.280146706857 + 0.011544409979) / (0.560525113891 * 114.869491162797))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13195]

end BstLean.Part269.N13195

/-! The original eight local profiles supply actual 13195 moment certificates. -/
namespace BstLean.Part269.N13195
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13195 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13195 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13195 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052288519498 ∧
    0 ≤ bN 13195 BstLean.Part154.csC (groupTheta g) ∧ bN 13195 BstLean.Part154.csC (groupTheta g) ≤ 0.001326841356 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13195 13195 0.011
      (momentAllowance 13195 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13195 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13195 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13195 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13195 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13195 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228666830778 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13195 0.011
      (momentAllowance 13195 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13195 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13195
/-! The actual computed-centre upper energy formula at 13195. -/
namespace BstLean.Part269.N13195
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13195

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13195
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13195)
open BstLean.Part268 (cell13195)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084163970774
  | 2 => 0.085086404344
  | 3 => 0.086004141895
  | 4 => 0.086917932900
  | 5 => 0.087828702504
  | 6 => 0.088737579858
  | 7 => 0.089645929554
  | 8 => 0.090555386279
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13195 13195 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13195 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13195

/-! Actual upper energy certificates on all 43 source endpoints at 13195. -/
namespace BstLean.Part269.N13195
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13195)
open BstLean.Part268 (cell13195)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13195 (gMinus 13195) (1 - (cell13195 i).lower) ≤ 1 ∧
    energyUpper 13195 (gMinus 13195) (BstLean.Part211.gPlus 13195)
      (finiteEnergy 13195 13195 0.011) (1 - (cell13195 i).lower) ≤
      (cell13195 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨10,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨11,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨12,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨13,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨14,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨15,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨16,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨17,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨18,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨19,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨20,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨21,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨22,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨23,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨24,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨25,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨26,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨27,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨28,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨29,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨30,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨31,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨32,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨33,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨34,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨35,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨36,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨37,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨38,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨39,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨40,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨41,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨42,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨43,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨44,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨45,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨46,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨47,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨48,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨49,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨50,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨51,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13195) (by norm_num)
        (q := 1 - (cell13195 ⟨52,by decide⟩).lower)
        (by norm_num [cell13195]) (by norm_num [cell13195])
      exact ⟨E.1,E.2.trans (by norm_num [cell13195])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13195

/-! Source-cell containment and simple scalar guards at 13195. -/
namespace BstLean.Part269.N13195
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13195)
open BstLean.Part268 (cell13195)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13195 ⟨10,by decide⟩).lower ∧ (cell13195 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13195 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13195 ⟨11,by decide⟩).lower ∧ (cell13195 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13195 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13195 ⟨12,by decide⟩).lower ∧ (cell13195 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13195 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13195 ⟨13,by decide⟩).lower ∧ (cell13195 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13195 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13195 ⟨14,by decide⟩).lower ∧ (cell13195 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13195 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13195 ⟨15,by decide⟩).lower ∧ (cell13195 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13195 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13195 ⟨16,by decide⟩).lower ∧ (cell13195 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13195 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13195 ⟨17,by decide⟩).lower ∧ (cell13195 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13195 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13195 ⟨18,by decide⟩).lower ∧ (cell13195 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13195 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13195 ⟨19,by decide⟩).lower ∧ (cell13195 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13195 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13195 ⟨20,by decide⟩).lower ∧ (cell13195 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13195 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13195 ⟨21,by decide⟩).lower ∧ (cell13195 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13195 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13195 ⟨22,by decide⟩).lower ∧ (cell13195 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13195 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13195 ⟨23,by decide⟩).lower ∧ (cell13195 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13195 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13195 ⟨24,by decide⟩).lower ∧ (cell13195 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13195 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13195 ⟨25,by decide⟩).lower ∧ (cell13195 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13195 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13195 ⟨26,by decide⟩).lower ∧ (cell13195 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13195 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13195 ⟨27,by decide⟩).lower ∧ (cell13195 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13195 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13195 ⟨28,by decide⟩).lower ∧ (cell13195 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13195 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13195 ⟨29,by decide⟩).lower ∧ (cell13195 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13195 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13195 ⟨30,by decide⟩).lower ∧ (cell13195 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13195 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13195 ⟨31,by decide⟩).lower ∧ (cell13195 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13195 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13195 ⟨32,by decide⟩).lower ∧ (cell13195 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13195 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13195 ⟨33,by decide⟩).lower ∧ (cell13195 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13195 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13195 ⟨34,by decide⟩).lower ∧ (cell13195 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13195 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13195 ⟨35,by decide⟩).lower ∧ (cell13195 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13195 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13195 ⟨36,by decide⟩).lower ∧ (cell13195 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13195 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13195 ⟨37,by decide⟩).lower ∧ (cell13195 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13195 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13195 ⟨38,by decide⟩).lower ∧ (cell13195 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13195 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13195 ⟨39,by decide⟩).lower ∧ (cell13195 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13195 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13195 ⟨40,by decide⟩).lower ∧ (cell13195 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13195 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13195 ⟨41,by decide⟩).lower ∧ (cell13195 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13195 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13195 ⟨42,by decide⟩).lower ∧ (cell13195 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13195 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13195 ⟨43,by decide⟩).lower ∧ (cell13195 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13195 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13195 ⟨44,by decide⟩).lower ∧ (cell13195 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13195 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13195 ⟨45,by decide⟩).lower ∧ (cell13195 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13195 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13195 ⟨46,by decide⟩).lower ∧ (cell13195 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13195 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13195 ⟨47,by decide⟩).lower ∧ (cell13195 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13195 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13195 ⟨48,by decide⟩).lower ∧ (cell13195 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13195 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13195 ⟨49,by decide⟩).lower ∧ (cell13195 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13195 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13195 ⟨50,by decide⟩).lower ∧ (cell13195 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13195 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13195 ⟨51,by decide⟩).lower ∧ (cell13195 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13195 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13195 ⟨52,by decide⟩).lower ∧ (cell13195 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13195 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13195 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13195 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13195,cell13195,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13195 i).lower ∧
    (cell13195 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13195 i).upper ≤ (0.532 : ℝ) ∧
    (cell13195 i).centre ≤ (0.1 : ℝ) ∧ (cell13195 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13195 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13195 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13195

/-! The local source numeric instances at 13195 have no network premises. -/
namespace BstLean.Part269.N13195
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13195)
open BstLean.Part268 (cell13195)

noncomputable def sourceNumerics13195 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13195 (cell13195 i)
      scalarRow13195.M scalarRow13195.H scalarRow13195.xi := by
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
    energy_allowance := scalarRow13195.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13195]
    centre_nonneg := (scalarRow13195.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13195])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13195
/-! Actual 13196 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13196
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13196 ≤ (1.035123929630 : ℝ) := by
  have hr : (114.873843846195 : ℝ) ≤ √(13196 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.873843846195 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13196 13196 (11 / 1000) ≤
    (0.008321188349 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13196) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.873843846195 : ℝ) ≤ √(13196 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13196)
  have hdiv : K / √(13196 : ℝ) ≤ K / 114.873843846195 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.873843846195 ≤ (0.008321188349 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13196.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13196 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13196 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13196 := gPlus_lower 13196
end BstLean.Part269.N13196

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13196
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035123929629 : ℝ) ≤ wn 13196 := by
  have hn : √(13196 : ℝ) ≤ 114.873843846196 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13196 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.873843846196 ≤ 2 / √(13196 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242253005 : ℝ) ≤ rhoBar 13196 BstLean.Part154.csC ∧
    rhoBar 13196 BstLean.Part154.csC ≤ 0.000242253380 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035123929629 : ℝ) / (1.295212 * 13196) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035123929630 : ℝ) / (1.29521 * 13196) := by gcongr
      _ ≤ (0.000242253380 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13196 BstLean.Part154.csC) ≤ 0.000969072207 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13196 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13196 BstLean.Part154.csC) (piBar (rhoBar 13196 BstLean.Part154.csC)) ≤ 0.000185034437 ∧
    cc1 (rhoBar 13196 BstLean.Part154.csC) (piBar (rhoBar 13196 BstLean.Part154.csC)) ≤ 0.000117738708 ∧
    cc2 (rhoBar 13196 BstLean.Part154.csC) ≤ 0.000068348305 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13196 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13196 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13196 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13196 BstLean.Part154.csC * nuR (rhoBar 13196 BstLean.Part154.csC)) ≤ 0.000484521432 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242253380 : ℝ) * 0.000969072207 := by gcongr
      _ ≤ (0.000484521432 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13196 BstLean.Part154.csC) * nuR (rhoBar 13196 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000969072207 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13196 BstLean.Part154.csC) * rhoBar 13196 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242253380 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242253380 / 2 + 0.399 * 0.000969072207 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185034437 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484521432 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117738708 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242253380 / 1.414213562 := by gcongr
      _ ≤ (0.000068348305 : ℝ) := by norm_num

end BstLean.Part269.N13196

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13196
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13196 BstLean.Part154.csC) (piBar (rhoBar 13196 BstLean.Part154.csC)) ≤ 1.47857E-7 := by
  have hr0 : 0 ≤ rhoBar 13196 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13196 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13196 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13196 BstLean.Part154.csC) (piBar (rhoBar 13196 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13196 BstLean.Part154.csC) (piBar (rhoBar 13196 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13196 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185034437 : ℝ) ^ 2 + 0.000117738708 ^ 2 + 3 * 0.000068348305 ^ 2 +
        2 * 0.797885 * 0.000185034437 * 0.000117738708 + 2 * 0.000185034437 * 0.000068348305 +
        4 * 0.797885 * 0.000117738708 * 0.000068348305 := by gcongr
    _ ≤ (1.47857E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13196 BstLean.Part154.csC Θ ≤ 0.002527115301 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13196 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13196 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13196 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13196 BstLean.Part154.csC) (piBar (rhoBar 13196 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13196 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035123929630 * 1.47857E-7 / (0.000242253005 : ℝ) := by gcongr
    _ ≤ 0.002527115301 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13196 BstLean.Part154.csC Θ ≤ 0.002802107850 + 0.000638561012 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13196 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13196 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13196 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035123929630 : ℝ) * ((2 * Θ * 0.000242253380 +
        (6863 / 10000) * 0.000242253380 * 13196 * 0.000969072207) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002802107850 + 0.000638561012 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13196 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13196 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13196 0.011 Θ ∧ gammaRatio 13196 0.011 Θ ≤ 0.000083280448 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13196 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035123929630 : ℝ) * 0.525 / ((1 - 0.011) * 13196) := by gcongr
      _ ≤ (0.000083280448 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13196 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13196 0.011 Θ) :=
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
    badAllowance 13196 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13196 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13196 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13196 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13196 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13196 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13196 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13196 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13196 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13196 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13196 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035123929630 : ℝ) * 13196 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13196 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003119584050 + 0.003165676313 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13196

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13196
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13196 BstLean.Part154.csC) (piBar (rhoBar 13196 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13196 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13196 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13196 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13196 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13196 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13196 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13196 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13196 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13196 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13196 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13196 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13196 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13196 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13196 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051477904704 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13196) ≤ 0.010396079222 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13196 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035123929630)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010396079222 + 2 * 0.737676 / 13196) := by gcongr
    _ ≤ (0.051477904704 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13196 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13196

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13196
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525155782 : ℝ) ≤ plow 13196 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13196) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052288164115)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326735534) : eMP 13196 0.011 xi bn ≤ 0.001142845429 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13196 : ℝ) * (1 - 0.011))) ≤ 0.000565129323 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001326735534 / (13196 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565129323 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565129323 : ℝ) + 3.141593 * 0.052288164115 / (13196 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001142845429 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052288164115)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326735534) : PiBarMP 13196 12 0.011 xi bn ≤ 0.158161805027 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13196 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036424381038 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.240290615876 : ℝ) ≤ √((13196 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.873843846195 : ℝ) ≤ √(13196 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13196) ≤ 0.121284426431 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036424381038 + 0.052288164115 * 1.772454 / (2 * (114.240290615876 : ℝ))) * (1 + 0.001142845429) +
        8 / (13196 * 114.873843846195) + 0.121284426431 := by gcongr
    _ ≤ (0.158161805027 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052288164115)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326735534) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280143958405) :
    parallelOracle 13196 0.011 xi bn cd ≤ 0.159115286339 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13196 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13196 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525155782 : ℝ) ≤ plow 13196 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.873843846195 : ℝ) ≤ √(13196 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280143958405 : ℝ) / (2 * 0.560525155782 * 114.873843846195)) * 0.158161805027 +
        0.280143958405 ^ 2 / (2 * 0.560525155782 * 114.873843846195) := by gcongr
    _ ≤ (0.159115286339 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052288164115) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326735534)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280143958405) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13196 13196 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525155782 : ℝ) ≤ plow 13196 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.873843846195 : ℝ) ≤ √(13196 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13196 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13196 Θ 1.22 ≤ 0.011543972550 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.873843846195 := by gcongr <;> linarith
      _ ≤ (0.011543972550 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13196 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13196 13196 0.011 ≤ 0.008321188349 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13196 13196 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13196 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13196 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13196 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13196 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159115286339 + 0.011543972550 + (0.008321188349 : ℝ) *
        (1 + 2 * (0.280143958405 + 0.011543972550) / (0.560525155782 * 114.873843846195))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13196]

end BstLean.Part269.N13196

/-! The original eight local profiles supply actual 13196 moment certificates. -/
namespace BstLean.Part269.N13196
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13196 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13196 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13196 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052288164115 ∧
    0 ≤ bN 13196 BstLean.Part154.csC (groupTheta g) ∧ bN 13196 BstLean.Part154.csC (groupTheta g) ≤ 0.001326735534 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13196 13196 0.011
      (momentAllowance 13196 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13196 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13196 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13196 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13196 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13196 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228666053701 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13196 0.011
      (momentAllowance 13196 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13196 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13196
/-! The actual computed-centre upper energy formula at 13196. -/
namespace BstLean.Part269.N13196
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13196

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13196
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13196)
open BstLean.Part268 (cell13196)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084161496883
  | 2 => 0.085083900823
  | 3 => 0.086001604675
  | 4 => 0.086915356931
  | 5 => 0.087826081569
  | 6 => 0.088734906367
  | 7 => 0.089643194304
  | 8 => 0.090552578190
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13196 13196 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13196 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13196

/-! Actual upper energy certificates on all 43 source endpoints at 13196. -/
namespace BstLean.Part269.N13196
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13196)
open BstLean.Part268 (cell13196)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13196 (gMinus 13196) (1 - (cell13196 i).lower) ≤ 1 ∧
    energyUpper 13196 (gMinus 13196) (BstLean.Part211.gPlus 13196)
      (finiteEnergy 13196 13196 0.011) (1 - (cell13196 i).lower) ≤
      (cell13196 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨10,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨11,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨12,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨13,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨14,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨15,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨16,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨17,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨18,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨19,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨20,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨21,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨22,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨23,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨24,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨25,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨26,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨27,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨28,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨29,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨30,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨31,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨32,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨33,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨34,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨35,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨36,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨37,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨38,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨39,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨40,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨41,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨42,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨43,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨44,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨45,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨46,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨47,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨48,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨49,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨50,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨51,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13196) (by norm_num)
        (q := 1 - (cell13196 ⟨52,by decide⟩).lower)
        (by norm_num [cell13196]) (by norm_num [cell13196])
      exact ⟨E.1,E.2.trans (by norm_num [cell13196])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13196

/-! Source-cell containment and simple scalar guards at 13196. -/
namespace BstLean.Part269.N13196
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13196)
open BstLean.Part268 (cell13196)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13196 ⟨10,by decide⟩).lower ∧ (cell13196 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13196 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13196 ⟨11,by decide⟩).lower ∧ (cell13196 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13196 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13196 ⟨12,by decide⟩).lower ∧ (cell13196 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13196 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13196 ⟨13,by decide⟩).lower ∧ (cell13196 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13196 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13196 ⟨14,by decide⟩).lower ∧ (cell13196 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13196 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13196 ⟨15,by decide⟩).lower ∧ (cell13196 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13196 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13196 ⟨16,by decide⟩).lower ∧ (cell13196 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13196 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13196 ⟨17,by decide⟩).lower ∧ (cell13196 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13196 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13196 ⟨18,by decide⟩).lower ∧ (cell13196 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13196 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13196 ⟨19,by decide⟩).lower ∧ (cell13196 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13196 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13196 ⟨20,by decide⟩).lower ∧ (cell13196 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13196 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13196 ⟨21,by decide⟩).lower ∧ (cell13196 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13196 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13196 ⟨22,by decide⟩).lower ∧ (cell13196 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13196 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13196 ⟨23,by decide⟩).lower ∧ (cell13196 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13196 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13196 ⟨24,by decide⟩).lower ∧ (cell13196 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13196 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13196 ⟨25,by decide⟩).lower ∧ (cell13196 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13196 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13196 ⟨26,by decide⟩).lower ∧ (cell13196 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13196 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13196 ⟨27,by decide⟩).lower ∧ (cell13196 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13196 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13196 ⟨28,by decide⟩).lower ∧ (cell13196 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13196 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13196 ⟨29,by decide⟩).lower ∧ (cell13196 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13196 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13196 ⟨30,by decide⟩).lower ∧ (cell13196 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13196 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13196 ⟨31,by decide⟩).lower ∧ (cell13196 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13196 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13196 ⟨32,by decide⟩).lower ∧ (cell13196 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13196 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13196 ⟨33,by decide⟩).lower ∧ (cell13196 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13196 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13196 ⟨34,by decide⟩).lower ∧ (cell13196 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13196 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13196 ⟨35,by decide⟩).lower ∧ (cell13196 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13196 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13196 ⟨36,by decide⟩).lower ∧ (cell13196 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13196 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13196 ⟨37,by decide⟩).lower ∧ (cell13196 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13196 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13196 ⟨38,by decide⟩).lower ∧ (cell13196 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13196 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13196 ⟨39,by decide⟩).lower ∧ (cell13196 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13196 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13196 ⟨40,by decide⟩).lower ∧ (cell13196 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13196 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13196 ⟨41,by decide⟩).lower ∧ (cell13196 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13196 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13196 ⟨42,by decide⟩).lower ∧ (cell13196 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13196 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13196 ⟨43,by decide⟩).lower ∧ (cell13196 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13196 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13196 ⟨44,by decide⟩).lower ∧ (cell13196 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13196 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13196 ⟨45,by decide⟩).lower ∧ (cell13196 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13196 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13196 ⟨46,by decide⟩).lower ∧ (cell13196 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13196 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13196 ⟨47,by decide⟩).lower ∧ (cell13196 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13196 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13196 ⟨48,by decide⟩).lower ∧ (cell13196 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13196 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13196 ⟨49,by decide⟩).lower ∧ (cell13196 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13196 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13196 ⟨50,by decide⟩).lower ∧ (cell13196 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13196 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13196 ⟨51,by decide⟩).lower ∧ (cell13196 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13196 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13196 ⟨52,by decide⟩).lower ∧ (cell13196 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13196 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13196 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13196 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13196,cell13196,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13196 i).lower ∧
    (cell13196 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13196 i).upper ≤ (0.532 : ℝ) ∧
    (cell13196 i).centre ≤ (0.1 : ℝ) ∧ (cell13196 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13196 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13196 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13196

/-! The local source numeric instances at 13196 have no network premises. -/
namespace BstLean.Part269.N13196
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13196)
open BstLean.Part268 (cell13196)

noncomputable def sourceNumerics13196 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13196 (cell13196 i)
      scalarRow13196.M scalarRow13196.H scalarRow13196.xi := by
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
    energy_allowance := scalarRow13196.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13196]
    centre_nonneg := (scalarRow13196.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13196])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13196
/-! Actual 13197 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13197
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13197 ≤ (1.035122587366 : ℝ) := by
  have hr : (114.878196364671 : ℝ) ≤ √(13197 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.878196364671 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13197 13197 (11 / 1000) ≤
    (0.008320873072 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13197) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.878196364671 : ℝ) ≤ √(13197 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13197)
  have hdiv : K / √(13197 : ℝ) ≤ K / 114.878196364671 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.878196364671 ≤ (0.008320873072 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13197.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13197 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13197 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13197 := gPlus_lower 13197
end BstLean.Part269.N13197

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13197
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035122587365 : ℝ) ≤ wn 13197 := by
  have hn : √(13197 : ℝ) ≤ 114.878196364672 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13197 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.878196364672 ≤ 2 / √(13197 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242234334 : ℝ) ≤ rhoBar 13197 BstLean.Part154.csC ∧
    rhoBar 13197 BstLean.Part154.csC ≤ 0.000242234709 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035122587365 : ℝ) / (1.295212 * 13197) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035122587366 : ℝ) / (1.29521 * 13197) := by gcongr
      _ ≤ (0.000242234709 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13197 BstLean.Part154.csC) ≤ 0.000968997514 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13197 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13197 BstLean.Part154.csC) (piBar (rhoBar 13197 BstLean.Part154.csC)) ≤ 0.000185020175 ∧
    cc1 (rhoBar 13197 BstLean.Part154.csC) (piBar (rhoBar 13197 BstLean.Part154.csC)) ≤ 0.000117729634 ∧
    cc2 (rhoBar 13197 BstLean.Part154.csC) ≤ 0.000068343037 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13197 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13197 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13197 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13197 BstLean.Part154.csC * nuR (rhoBar 13197 BstLean.Part154.csC)) ≤ 0.000484484088 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242234709 : ℝ) * 0.000968997514 := by gcongr
      _ ≤ (0.000484484088 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13197 BstLean.Part154.csC) * nuR (rhoBar 13197 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000968997514 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13197 BstLean.Part154.csC) * rhoBar 13197 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242234709 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242234709 / 2 + 0.399 * 0.000968997514 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185020175 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484484088 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117729634 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242234709 / 1.414213562 := by gcongr
      _ ≤ (0.000068343037 : ℝ) := by norm_num

end BstLean.Part269.N13197

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13197
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13197 BstLean.Part154.csC) (piBar (rhoBar 13197 BstLean.Part154.csC)) ≤ 1.47834E-7 := by
  have hr0 : 0 ≤ rhoBar 13197 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13197 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13197 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13197 BstLean.Part154.csC) (piBar (rhoBar 13197 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13197 BstLean.Part154.csC) (piBar (rhoBar 13197 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13197 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185020175 : ℝ) ^ 2 + 0.000117729634 ^ 2 + 3 * 0.000068343037 ^ 2 +
        2 * 0.797885 * 0.000185020175 * 0.000117729634 + 2 * 0.000185020175 * 0.000068343037 +
        4 * 0.797885 * 0.000117729634 * 0.000068343037 := by gcongr
    _ ≤ (1.47834E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13197 BstLean.Part154.csC Θ ≤ 0.002526913672 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13197 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13197 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13197 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13197 BstLean.Part154.csC) (piBar (rhoBar 13197 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13197 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035122587366 * 1.47834E-7 / (0.000242234334 : ℝ) := by gcongr
    _ ≤ 0.002526913672 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13197 BstLean.Part154.csC Θ ≤ 0.002801884604 + 0.000638510969 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13197 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13197 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13197 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035122587366 : ℝ) * ((2 * Θ * 0.000242234709 +
        (6863 / 10000) * 0.000242234709 * 13197 * 0.000968997514) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002801884604 + 0.000638510969 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13197 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13197 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13197 0.011 Θ ∧ gammaRatio 13197 0.011 Θ ≤ 0.000083274029 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13197 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035122587366 : ℝ) * 0.525 / ((1 - 0.011) * 13197) := by gcongr
      _ ≤ (0.000083274029 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13197 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13197 0.011 Θ) :=
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
    badAllowance 13197 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13197 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13197 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13197 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13197 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13197 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13197 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13197 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13197 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13197 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13197 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035122587366 : ℝ) * 13197 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13197 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003119360804 + 0.003165424641 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13197

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13197
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13197 BstLean.Part154.csC) (piBar (rhoBar 13197 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13197 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13197 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13197 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13197 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13197 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13197 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13197 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13197 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13197 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13197 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13197 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13197 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13197 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13197 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051475933552 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13197) ≤ 0.010395685334 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13197 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035122587366)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010395685334 + 2 * 0.737676 / 13197) := by gcongr
    _ ≤ (0.051475933552 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13197 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13197

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13197
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525197666 : ℝ) ≤ plow 13197 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13197) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052287808741)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326629678) : eMP 13197 0.011 xi bn ≤ 0.001142756475 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13197 : ℝ) * (1 - 0.011))) ≤ 0.000565085366 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001326629678 / (13197 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565085366 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565085366 : ℝ) + 3.141593 * 0.052287808741 / (13197 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001142756475 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052287808741)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326629678) : PiBarMP 13197 12 0.011 xi bn ≤ 0.158155732986 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13197 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036422927917 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.244619129305 : ℝ) ≤ √((13197 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.878196364671 : ℝ) ≤ √(13197 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13197) ≤ 0.121279831193 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036422927917 + 0.052287808741 * 1.772454 / (2 * (114.244619129305 : ℝ))) * (1 + 0.001142756475) +
        8 / (13197 * 114.878196364671) + 0.121279831193 := by gcongr
    _ ≤ (0.158155732986 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052287808741)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326629678) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280141210193) :
    parallelOracle 13197 0.011 xi bn cd ≤ 0.159109149561 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13197 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13197 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525197666 : ℝ) ≤ plow 13197 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.878196364671 : ℝ) ≤ √(13197 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280141210193 : ℝ) / (2 * 0.560525197666 * 114.878196364671)) * 0.158155732986 +
        0.280141210193 ^ 2 / (2 * 0.560525197666 * 114.878196364671) := by gcongr
    _ ≤ (0.159109149561 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052287808741) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326629678)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280141210193) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13197 13197 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525197666 : ℝ) ≤ plow 13197 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.878196364671 : ℝ) ≤ √(13197 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13197 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13197 Θ 1.22 ≤ 0.011543535170 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.878196364671 := by gcongr <;> linarith
      _ ≤ (0.011543535170 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13197 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13197 13197 0.011 ≤ 0.008320873072 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13197 13197 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13197 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13197 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13197 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13197 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159109149561 + 0.011543535170 + (0.008320873072 : ℝ) *
        (1 + 2 * (0.280141210193 + 0.011543535170) / (0.560525197666 * 114.878196364671))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13197]

end BstLean.Part269.N13197

/-! The original eight local profiles supply actual 13197 moment certificates. -/
namespace BstLean.Part269.N13197
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13197 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13197 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13197 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052287808741 ∧
    0 ≤ bN 13197 BstLean.Part154.csC (groupTheta g) ∧ bN 13197 BstLean.Part154.csC (groupTheta g) ≤ 0.001326629678 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13197 13197 0.011
      (momentAllowance 13197 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13197 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13197 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13197 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13197 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13197 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228665276641 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13197 0.011
      (momentAllowance 13197 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13197 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13197
/-! The actual computed-centre upper energy formula at 13197. -/
namespace BstLean.Part269.N13197
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13197

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13197
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13197)
open BstLean.Part268 (cell13197)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084159023671
  | 2 => 0.085081398002
  | 3 => 0.085999068183
  | 4 => 0.086912781723
  | 5 => 0.087823461438
  | 6 => 0.088732233731
  | 7 => 0.089640459972
  | 8 => 0.090549771094
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13197 13197 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13197 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13197

/-! Actual upper energy certificates on all 43 source endpoints at 13197. -/
namespace BstLean.Part269.N13197
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13197)
open BstLean.Part268 (cell13197)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13197 (gMinus 13197) (1 - (cell13197 i).lower) ≤ 1 ∧
    energyUpper 13197 (gMinus 13197) (BstLean.Part211.gPlus 13197)
      (finiteEnergy 13197 13197 0.011) (1 - (cell13197 i).lower) ≤
      (cell13197 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨10,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨11,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨12,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨13,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨14,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨15,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨16,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨17,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨18,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨19,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨20,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨21,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨22,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨23,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨24,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨25,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨26,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨27,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨28,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨29,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨30,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨31,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨32,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨33,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨34,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨35,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨36,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨37,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨38,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨39,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨40,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨41,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨42,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨43,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨44,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨45,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨46,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨47,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨48,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨49,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨50,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨51,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13197) (by norm_num)
        (q := 1 - (cell13197 ⟨52,by decide⟩).lower)
        (by norm_num [cell13197]) (by norm_num [cell13197])
      exact ⟨E.1,E.2.trans (by norm_num [cell13197])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13197

/-! Source-cell containment and simple scalar guards at 13197. -/
namespace BstLean.Part269.N13197
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13197)
open BstLean.Part268 (cell13197)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13197 ⟨10,by decide⟩).lower ∧ (cell13197 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13197 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13197 ⟨11,by decide⟩).lower ∧ (cell13197 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13197 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13197 ⟨12,by decide⟩).lower ∧ (cell13197 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13197 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13197 ⟨13,by decide⟩).lower ∧ (cell13197 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13197 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13197 ⟨14,by decide⟩).lower ∧ (cell13197 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13197 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13197 ⟨15,by decide⟩).lower ∧ (cell13197 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13197 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13197 ⟨16,by decide⟩).lower ∧ (cell13197 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13197 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13197 ⟨17,by decide⟩).lower ∧ (cell13197 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13197 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13197 ⟨18,by decide⟩).lower ∧ (cell13197 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13197 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13197 ⟨19,by decide⟩).lower ∧ (cell13197 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13197 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13197 ⟨20,by decide⟩).lower ∧ (cell13197 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13197 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13197 ⟨21,by decide⟩).lower ∧ (cell13197 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13197 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13197 ⟨22,by decide⟩).lower ∧ (cell13197 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13197 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13197 ⟨23,by decide⟩).lower ∧ (cell13197 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13197 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13197 ⟨24,by decide⟩).lower ∧ (cell13197 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13197 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13197 ⟨25,by decide⟩).lower ∧ (cell13197 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13197 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13197 ⟨26,by decide⟩).lower ∧ (cell13197 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13197 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13197 ⟨27,by decide⟩).lower ∧ (cell13197 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13197 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13197 ⟨28,by decide⟩).lower ∧ (cell13197 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13197 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13197 ⟨29,by decide⟩).lower ∧ (cell13197 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13197 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13197 ⟨30,by decide⟩).lower ∧ (cell13197 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13197 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13197 ⟨31,by decide⟩).lower ∧ (cell13197 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13197 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13197 ⟨32,by decide⟩).lower ∧ (cell13197 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13197 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13197 ⟨33,by decide⟩).lower ∧ (cell13197 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13197 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13197 ⟨34,by decide⟩).lower ∧ (cell13197 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13197 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13197 ⟨35,by decide⟩).lower ∧ (cell13197 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13197 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13197 ⟨36,by decide⟩).lower ∧ (cell13197 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13197 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13197 ⟨37,by decide⟩).lower ∧ (cell13197 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13197 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13197 ⟨38,by decide⟩).lower ∧ (cell13197 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13197 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13197 ⟨39,by decide⟩).lower ∧ (cell13197 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13197 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13197 ⟨40,by decide⟩).lower ∧ (cell13197 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13197 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13197 ⟨41,by decide⟩).lower ∧ (cell13197 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13197 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13197 ⟨42,by decide⟩).lower ∧ (cell13197 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13197 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13197 ⟨43,by decide⟩).lower ∧ (cell13197 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13197 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13197 ⟨44,by decide⟩).lower ∧ (cell13197 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13197 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13197 ⟨45,by decide⟩).lower ∧ (cell13197 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13197 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13197 ⟨46,by decide⟩).lower ∧ (cell13197 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13197 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13197 ⟨47,by decide⟩).lower ∧ (cell13197 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13197 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13197 ⟨48,by decide⟩).lower ∧ (cell13197 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13197 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13197 ⟨49,by decide⟩).lower ∧ (cell13197 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13197 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13197 ⟨50,by decide⟩).lower ∧ (cell13197 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13197 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13197 ⟨51,by decide⟩).lower ∧ (cell13197 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13197 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13197 ⟨52,by decide⟩).lower ∧ (cell13197 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13197 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13197 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13197 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13197,cell13197,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13197 i).lower ∧
    (cell13197 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13197 i).upper ≤ (0.532 : ℝ) ∧
    (cell13197 i).centre ≤ (0.1 : ℝ) ∧ (cell13197 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13197 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13197 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13197

/-! The local source numeric instances at 13197 have no network premises. -/
namespace BstLean.Part269.N13197
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13197)
open BstLean.Part268 (cell13197)

noncomputable def sourceNumerics13197 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13197 (cell13197 i)
      scalarRow13197.M scalarRow13197.H scalarRow13197.xi := by
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
    energy_allowance := scalarRow13197.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13197]
    centre_nonneg := (scalarRow13197.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13197])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13197
/-! Actual 13198 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13198
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13198 ≤ (1.035121245255 : ℝ) := by
  have hr : (114.882548718245 : ℝ) ≤ √(13198 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.882548718245 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13198 13198 (11 / 1000) ≤
    (0.008320557832 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13198) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.882548718245 : ℝ) ≤ √(13198 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13198)
  have hdiv : K / √(13198 : ℝ) ≤ K / 114.882548718245 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.882548718245 ≤ (0.008320557832 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13198.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13198 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13198 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13198 := gPlus_lower 13198
end BstLean.Part269.N13198

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13198
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035121245254 : ℝ) ≤ wn 13198 := by
  have hn : √(13198 : ℝ) ≤ 114.882548718246 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13198 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.882548718246 ≤ 2 / √(13198 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242215666 : ℝ) ≤ rhoBar 13198 BstLean.Part154.csC ∧
    rhoBar 13198 BstLean.Part154.csC ≤ 0.000242216041 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035121245254 : ℝ) / (1.295212 * 13198) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035121245255 : ℝ) / (1.29521 * 13198) := by gcongr
      _ ≤ (0.000242216041 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13198 BstLean.Part154.csC) ≤ 0.000968922833 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13198 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13198 BstLean.Part154.csC) (piBar (rhoBar 13198 BstLean.Part154.csC)) ≤ 0.000185005916 ∧
    cc1 (rhoBar 13198 BstLean.Part154.csC) (piBar (rhoBar 13198 BstLean.Part154.csC)) ≤ 0.000117720561 ∧
    cc2 (rhoBar 13198 BstLean.Part154.csC) ≤ 0.000068337770 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13198 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13198 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13198 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13198 BstLean.Part154.csC * nuR (rhoBar 13198 BstLean.Part154.csC)) ≤ 0.000484446750 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242216041 : ℝ) * 0.000968922833 := by gcongr
      _ ≤ (0.000484446750 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13198 BstLean.Part154.csC) * nuR (rhoBar 13198 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000968922833 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13198 BstLean.Part154.csC) * rhoBar 13198 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242216041 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242216041 / 2 + 0.399 * 0.000968922833 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185005916 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484446750 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117720561 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242216041 / 1.414213562 := by gcongr
      _ ≤ (0.000068337770 : ℝ) := by norm_num

end BstLean.Part269.N13198

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13198
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13198 BstLean.Part154.csC) (piBar (rhoBar 13198 BstLean.Part154.csC)) ≤ 1.47811E-7 := by
  have hr0 : 0 ≤ rhoBar 13198 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13198 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13198 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13198 BstLean.Part154.csC) (piBar (rhoBar 13198 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13198 BstLean.Part154.csC) (piBar (rhoBar 13198 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13198 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185005916 : ℝ) ^ 2 + 0.000117720561 ^ 2 + 3 * 0.000068337770 ^ 2 +
        2 * 0.797885 * 0.000185005916 * 0.000117720561 + 2 * 0.000185005916 * 0.000068337770 +
        4 * 0.797885 * 0.000117720561 * 0.000068337770 := by gcongr
    _ ≤ (1.47811E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13198 BstLean.Part154.csC Θ ≤ 0.002526711983 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13198 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13198 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13198 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13198 BstLean.Part154.csC) (piBar (rhoBar 13198 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13198 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035121245255 * 1.47811E-7 / (0.000242215666 : ℝ) := by gcongr
    _ ≤ 0.002526711983 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13198 BstLean.Part154.csC Θ ≤ 0.002801661396 + 0.000638460934 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13198 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13198 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13198 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035121245255 : ℝ) * ((2 * Θ * 0.000242216041 +
        (6863 / 10000) * 0.000242216041 * 13198 * 0.000968922833) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002801661396 + 0.000638460934 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13198 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13198 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13198 0.011 Θ ∧ gammaRatio 13198 0.011 Θ ≤ 0.000083267612 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13198 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035121245255 : ℝ) * 0.525 / ((1 - 0.011) * 13198) := by gcongr
      _ ≤ (0.000083267612 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13198 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13198 0.011 Θ) :=
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
    badAllowance 13198 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13198 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13198 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13198 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13198 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13198 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13198 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13198 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13198 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13198 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13198 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035121245255 : ℝ) * 13198 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13198 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003119137596 + 0.003165172917 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13198

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13198
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13198 BstLean.Part154.csC) (piBar (rhoBar 13198 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13198 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13198 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13198 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13198 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13198 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13198 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13198 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13198 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13198 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13198 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13198 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13198 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13198 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13198 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051473962625 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13198) ≤ 0.010395291491 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13198 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035121245255)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010395291491 + 2 * 0.737676 / 13198) := by gcongr
    _ ≤ (0.051473962625 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13198 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13198

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13198
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525239543 : ℝ) ≤ plow 13198 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13198) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052287453378)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326523792) : eMP 13198 0.011 xi bn ≤ 0.001142667518 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13198 : ℝ) * (1 - 0.011))) ≤ 0.000565041407 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001326523792 / (13198 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000565041407 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000565041407 : ℝ) + 3.141593 * 0.052287453378 / (13198 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001142667518 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052287453378)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326523792) : PiBarMP 13198 12 0.011 xi bn ≤ 0.158149660996 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13198 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036421474325 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.248947478740 : ℝ) ≤ √((13198 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.882548718245 : ℝ) ≤ √(13198 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13198) ≤ 0.121275236476 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036421474325 + 0.052287453378 * 1.772454 / (2 * (114.248947478740 : ℝ))) * (1 + 0.001142667518) +
        8 / (13198 * 114.882548718245) + 0.121275236476 := by gcongr
    _ ≤ (0.158149660996 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052287453378)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326523792) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280138462227) :
    parallelOracle 13198 0.011 xi bn cd ≤ 0.159103012843 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13198 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13198 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525239543 : ℝ) ≤ plow 13198 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.882548718245 : ℝ) ≤ √(13198 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280138462227 : ℝ) / (2 * 0.560525239543 * 114.882548718245)) * 0.158149660996 +
        0.280138462227 ^ 2 / (2 * 0.560525239543 * 114.882548718245) := by gcongr
    _ ≤ (0.159103012843 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052287453378) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326523792)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280138462227) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13198 13198 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525239543 : ℝ) ≤ plow 13198 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.882548718245 : ℝ) ≤ √(13198 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13198 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13198 Θ 1.22 ≤ 0.011543097841 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.882548718245 := by gcongr <;> linarith
      _ ≤ (0.011543097841 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13198 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13198 13198 0.011 ≤ 0.008320557832 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13198 13198 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13198 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13198 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13198 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13198 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159103012843 + 0.011543097841 + (0.008320557832 : ℝ) *
        (1 + 2 * (0.280138462227 + 0.011543097841) / (0.560525239543 * 114.882548718245))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13198]

end BstLean.Part269.N13198

/-! The original eight local profiles supply actual 13198 moment certificates. -/
namespace BstLean.Part269.N13198
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13198 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13198 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13198 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052287453378 ∧
    0 ≤ bN 13198 BstLean.Part154.csC (groupTheta g) ∧ bN 13198 BstLean.Part154.csC (groupTheta g) ≤ 0.001326523792 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13198 13198 0.011
      (momentAllowance 13198 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13198 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13198 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13198 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13198 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13198 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228664499602 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13198 0.011
      (momentAllowance 13198 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13198 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13198
/-! The actual computed-centre upper energy formula at 13198. -/
namespace BstLean.Part269.N13198
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13198

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13198
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13198)
open BstLean.Part268 (cell13198)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084156551135
  | 2 => 0.085078895881
  | 3 => 0.085996532418
  | 4 => 0.086910207277
  | 5 => 0.087820842110
  | 6 => 0.088729561949
  | 7 => 0.089637726556
  | 8 => 0.090546964990
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13198 13198 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13198 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13198

/-! Actual upper energy certificates on all 43 source endpoints at 13198. -/
namespace BstLean.Part269.N13198
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13198)
open BstLean.Part268 (cell13198)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13198 (gMinus 13198) (1 - (cell13198 i).lower) ≤ 1 ∧
    energyUpper 13198 (gMinus 13198) (BstLean.Part211.gPlus 13198)
      (finiteEnergy 13198 13198 0.011) (1 - (cell13198 i).lower) ≤
      (cell13198 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨10,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨11,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨12,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨13,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨14,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨15,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨16,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨17,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨18,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨19,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨20,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨21,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨22,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨23,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨24,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨25,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨26,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨27,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨28,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨29,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨30,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨31,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨32,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨33,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨34,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨35,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨36,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨37,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨38,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨39,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨40,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨41,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨42,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨43,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨44,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨45,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨46,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨47,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨48,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨49,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨50,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨51,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13198) (by norm_num)
        (q := 1 - (cell13198 ⟨52,by decide⟩).lower)
        (by norm_num [cell13198]) (by norm_num [cell13198])
      exact ⟨E.1,E.2.trans (by norm_num [cell13198])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13198

/-! Source-cell containment and simple scalar guards at 13198. -/
namespace BstLean.Part269.N13198
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13198)
open BstLean.Part268 (cell13198)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13198 ⟨10,by decide⟩).lower ∧ (cell13198 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13198 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13198 ⟨11,by decide⟩).lower ∧ (cell13198 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13198 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13198 ⟨12,by decide⟩).lower ∧ (cell13198 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13198 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13198 ⟨13,by decide⟩).lower ∧ (cell13198 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13198 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13198 ⟨14,by decide⟩).lower ∧ (cell13198 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13198 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13198 ⟨15,by decide⟩).lower ∧ (cell13198 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13198 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13198 ⟨16,by decide⟩).lower ∧ (cell13198 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13198 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13198 ⟨17,by decide⟩).lower ∧ (cell13198 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13198 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13198 ⟨18,by decide⟩).lower ∧ (cell13198 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13198 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13198 ⟨19,by decide⟩).lower ∧ (cell13198 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13198 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13198 ⟨20,by decide⟩).lower ∧ (cell13198 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13198 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13198 ⟨21,by decide⟩).lower ∧ (cell13198 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13198 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13198 ⟨22,by decide⟩).lower ∧ (cell13198 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13198 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13198 ⟨23,by decide⟩).lower ∧ (cell13198 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13198 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13198 ⟨24,by decide⟩).lower ∧ (cell13198 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13198 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13198 ⟨25,by decide⟩).lower ∧ (cell13198 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13198 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13198 ⟨26,by decide⟩).lower ∧ (cell13198 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13198 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13198 ⟨27,by decide⟩).lower ∧ (cell13198 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13198 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13198 ⟨28,by decide⟩).lower ∧ (cell13198 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13198 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13198 ⟨29,by decide⟩).lower ∧ (cell13198 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13198 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13198 ⟨30,by decide⟩).lower ∧ (cell13198 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13198 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13198 ⟨31,by decide⟩).lower ∧ (cell13198 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13198 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13198 ⟨32,by decide⟩).lower ∧ (cell13198 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13198 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13198 ⟨33,by decide⟩).lower ∧ (cell13198 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13198 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13198 ⟨34,by decide⟩).lower ∧ (cell13198 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13198 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13198 ⟨35,by decide⟩).lower ∧ (cell13198 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13198 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13198 ⟨36,by decide⟩).lower ∧ (cell13198 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13198 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13198 ⟨37,by decide⟩).lower ∧ (cell13198 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13198 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13198 ⟨38,by decide⟩).lower ∧ (cell13198 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13198 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13198 ⟨39,by decide⟩).lower ∧ (cell13198 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13198 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13198 ⟨40,by decide⟩).lower ∧ (cell13198 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13198 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13198 ⟨41,by decide⟩).lower ∧ (cell13198 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13198 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13198 ⟨42,by decide⟩).lower ∧ (cell13198 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13198 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13198 ⟨43,by decide⟩).lower ∧ (cell13198 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13198 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13198 ⟨44,by decide⟩).lower ∧ (cell13198 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13198 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13198 ⟨45,by decide⟩).lower ∧ (cell13198 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13198 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13198 ⟨46,by decide⟩).lower ∧ (cell13198 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13198 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13198 ⟨47,by decide⟩).lower ∧ (cell13198 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13198 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13198 ⟨48,by decide⟩).lower ∧ (cell13198 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13198 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13198 ⟨49,by decide⟩).lower ∧ (cell13198 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13198 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13198 ⟨50,by decide⟩).lower ∧ (cell13198 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13198 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13198 ⟨51,by decide⟩).lower ∧ (cell13198 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13198 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13198 ⟨52,by decide⟩).lower ∧ (cell13198 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13198 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13198 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13198 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13198,cell13198,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13198 i).lower ∧
    (cell13198 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13198 i).upper ≤ (0.532 : ℝ) ∧
    (cell13198 i).centre ≤ (0.1 : ℝ) ∧ (cell13198 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13198 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13198 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13198

/-! The local source numeric instances at 13198 have no network premises. -/
namespace BstLean.Part269.N13198
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13198)
open BstLean.Part268 (cell13198)

noncomputable def sourceNumerics13198 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13198 (cell13198 i)
      scalarRow13198.M scalarRow13198.H scalarRow13198.xi := by
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
    energy_allowance := scalarRow13198.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13198]
    centre_nonneg := (scalarRow13198.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13198])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13198
/-! Actual 13199 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13199
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13199 ≤ (1.035119903298 : ℝ) := by
  have hr : (114.886900906935 : ℝ) ≤ √(13199 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.886900906935 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13199 13199 (11 / 1000) ≤
    (0.008320242627 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13199) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.886900906935 : ℝ) ≤ √(13199 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13199)
  have hdiv : K / √(13199 : ℝ) ≤ K / 114.886900906935 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.886900906935 ≤ (0.008320242627 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13199.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13199 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13199 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13199 := gPlus_lower 13199
end BstLean.Part269.N13199

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13199
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035119903297 : ℝ) ≤ wn 13199 := by
  have hn : √(13199 : ℝ) ≤ 114.886900906936 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13199 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.886900906936 ≤ 2 / √(13199 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242197001 : ℝ) ≤ rhoBar 13199 BstLean.Part154.csC ∧
    rhoBar 13199 BstLean.Part154.csC ≤ 0.000242197376 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035119903297 : ℝ) / (1.295212 * 13199) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035119903298 : ℝ) / (1.29521 * 13199) := by gcongr
      _ ≤ (0.000242197376 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13199 BstLean.Part154.csC) ≤ 0.000968848164 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13199 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13199 BstLean.Part154.csC) (piBar (rhoBar 13199 BstLean.Part154.csC)) ≤ 0.000184991659 ∧
    cc1 (rhoBar 13199 BstLean.Part154.csC) (piBar (rhoBar 13199 BstLean.Part154.csC)) ≤ 0.000117711489 ∧
    cc2 (rhoBar 13199 BstLean.Part154.csC) ≤ 0.000068332504 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13199 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13199 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13199 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13199 BstLean.Part154.csC * nuR (rhoBar 13199 BstLean.Part154.csC)) ≤ 0.000484409417 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242197376 : ℝ) * 0.000968848164 := by gcongr
      _ ≤ (0.000484409417 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13199 BstLean.Part154.csC) * nuR (rhoBar 13199 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000968848164 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13199 BstLean.Part154.csC) * rhoBar 13199 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242197376 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242197376 / 2 + 0.399 * 0.000968848164 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184991659 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000484409417 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117711489 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242197376 / 1.414213562 := by gcongr
      _ ≤ (0.000068332504 : ℝ) := by norm_num

end BstLean.Part269.N13199

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13199
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13199 BstLean.Part154.csC) (piBar (rhoBar 13199 BstLean.Part154.csC)) ≤ 1.47788E-7 := by
  have hr0 : 0 ≤ rhoBar 13199 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13199 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13199 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13199 BstLean.Part154.csC) (piBar (rhoBar 13199 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13199 BstLean.Part154.csC) (piBar (rhoBar 13199 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13199 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184991659 : ℝ) ^ 2 + 0.000117711489 ^ 2 + 3 * 0.000068332504 ^ 2 +
        2 * 0.797885 * 0.000184991659 * 0.000117711489 + 2 * 0.000184991659 * 0.000068332504 +
        4 * 0.797885 * 0.000117711489 * 0.000068332504 := by gcongr
    _ ≤ (1.47788E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13199 BstLean.Part154.csC Θ ≤ 0.002526510232 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13199 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13199 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13199 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13199 BstLean.Part154.csC) (piBar (rhoBar 13199 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13199 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035119903298 * 1.47788E-7 / (0.000242197001 : ℝ) := by gcongr
    _ ≤ 0.002526510232 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13199 BstLean.Part154.csC Θ ≤ 0.002801438226 + 0.000638410907 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13199 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13199 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13199 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035119903298 : ℝ) * ((2 * Θ * 0.000242197376 +
        (6863 / 10000) * 0.000242197376 * 13199 * 0.000968848164) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002801438226 + 0.000638410907 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13199 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13199 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13199 0.011 Θ ∧ gammaRatio 13199 0.011 Θ ≤ 0.000083261195 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13199 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035119903298 : ℝ) * 0.525 / ((1 - 0.011) * 13199) := by gcongr
      _ ≤ (0.000083261195 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13199 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13199 0.011 Θ) :=
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
    badAllowance 13199 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000317476200 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13199 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13199 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13199 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13199 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13199 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13199 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13199 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13199 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13199 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13199 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035119903298 : ℝ) * 13199 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000317476200 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13199 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003118914426 + 0.003164921139 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13199

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13199
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13199 BstLean.Part154.csC) (piBar (rhoBar 13199 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13199 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13199 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13199 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13199 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13199 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13199 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13199 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13199 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13199 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13199 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13199 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13199 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13199 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13199 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051471991921 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13199) ≤ 0.010394897692 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13199 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035119903298)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010394897692 + 2 * 0.737676 / 13199) := by gcongr
    _ ≤ (0.051471991921 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13199 12 ≤ 0.0015 := by
  exact BstLean.Part269.S33.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13199

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13199
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560525281415 : ℝ) ≤ plow 13199 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13199) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052287098024)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326417872) : eMP 13199 0.011 xi bn ≤ 0.001142578553 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13199 : ℝ) * (1 - 0.011))) ≤ 0.000564997444 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001326417872 / (13199 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000564997444 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000564997444 : ℝ) + 3.141593 * 0.052287098024 / (13199 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001142578553 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052287098024)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326417872) : PiBarMP 13199 12 0.011 xi bn ≤ 0.158143589007 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13199 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036420020209 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.253275664201 : ℝ) ≤ √((13199 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.886900906935 : ℝ) ≤ √(13199 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13199) ≤ 0.121270642282 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036420020209 + 0.052287098024 * 1.772454 / (2 * (114.253275664201 : ℝ))) * (1 + 0.001142578553) +
        8 / (13199 * 114.886900906935) + 0.121270642282 := by gcongr
    _ ≤ (0.158143589007 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052287098024)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326417872) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280135714501) :
    parallelOracle 13199 0.011 xi bn cd ≤ 0.159096876133 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13199 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13199 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560525281415 : ℝ) ≤ plow 13199 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.886900906935 : ℝ) ≤ √(13199 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280135714501 : ℝ) / (2 * 0.560525281415 * 114.886900906935)) * 0.158143589007 +
        0.280135714501 ^ 2 / (2 * 0.560525281415 * 114.886900906935) := by gcongr
    _ ≤ (0.159096876133 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052287098024) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001326417872)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280135714501) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13199 13199 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560525281415 : ℝ) ≤ plow 13199 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.886900906935 : ℝ) ≤ √(13199 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13199 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13199 Θ 1.22 ≤ 0.011542660561 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.886900906935 := by gcongr <;> linarith
      _ ≤ (0.011542660561 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13199 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13199 13199 0.011 ≤ 0.008320242627 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13199 13199 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13199 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13199 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13199 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13199 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159096876133 + 0.011542660561 + (0.008320242627 : ℝ) *
        (1 + 2 * (0.280135714501 + 0.011542660561) / (0.560525281415 * 114.886900906935))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13199]

end BstLean.Part269.N13199

/-! The original eight local profiles supply actual 13199 moment certificates. -/
namespace BstLean.Part269.N13199
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13199 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13199 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13199 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052287098024 ∧
    0 ≤ bN 13199 BstLean.Part154.csC (groupTheta g) ∧ bN 13199 BstLean.Part154.csC (groupTheta g) ≤ 0.001326417872 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13199 13199 0.011
      (momentAllowance 13199 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13199 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13199 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13199 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13199 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13199 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228663722580 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13199 0.011
      (momentAllowance 13199 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13199 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13199
/-! The actual computed-centre upper energy formula at 13199. -/
namespace BstLean.Part269.N13199
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13199

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13199
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13199)
open BstLean.Part268 (cell13199)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084154079277
  | 2 => 0.085076394459
  | 3 => 0.085993997379
  | 4 => 0.086907633590
  | 5 => 0.087818223585
  | 6 => 0.088726891021
  | 7 => 0.089634994055
  | 8 => 0.090544159877
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13199 13199 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13199 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003124280256 + 0.003170898306 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S33.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S33.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13199

/-! Actual upper energy certificates on all 43 source endpoints at 13199. -/
namespace BstLean.Part269.N13199
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13199)
open BstLean.Part268 (cell13199)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13199 (gMinus 13199) (1 - (cell13199 i).lower) ≤ 1 ∧
    energyUpper 13199 (gMinus 13199) (BstLean.Part211.gPlus 13199)
      (finiteEnergy 13199 13199 0.011) (1 - (cell13199 i).lower) ≤
      (cell13199 i).energy := by
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
      have E := BstLean.Part269.S33.uniformEnergy10 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨10,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy11 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨11,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy12 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨12,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy13 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨13,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy14 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨14,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy15 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨15,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy16 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨16,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy17 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨17,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy18 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨18,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy19 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨19,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy20 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨20,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy21 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨21,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy22 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨22,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy23 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨23,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy24 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨24,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy25 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨25,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy26 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨26,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy27 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨27,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy28 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨28,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy29 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨29,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy30 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨30,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy31 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨31,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy32 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨32,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy33 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨33,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy34 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨34,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy35 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨35,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy36 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨36,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy37 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨37,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy38 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨38,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy39 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨39,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy40 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨40,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy41 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨41,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy42 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨42,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy43 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨43,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy44 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨44,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy45 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨45,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy46 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨46,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy47 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨47,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy48 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨48,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy49 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨49,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy50 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨50,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy51 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨51,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S33.uniformEnergy52 (n := 13199) (by norm_num)
        (q := 1 - (cell13199 ⟨52,by decide⟩).lower)
        (by norm_num [cell13199]) (by norm_num [cell13199])
      exact ⟨E.1,E.2.trans (by norm_num [cell13199])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13199

/-! Source-cell containment and simple scalar guards at 13199. -/
namespace BstLean.Part269.N13199
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13199)
open BstLean.Part268 (cell13199)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13199 ⟨10,by decide⟩).lower ∧ (cell13199 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13199 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13199 ⟨11,by decide⟩).lower ∧ (cell13199 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13199 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13199 ⟨12,by decide⟩).lower ∧ (cell13199 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13199 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13199 ⟨13,by decide⟩).lower ∧ (cell13199 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13199 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13199 ⟨14,by decide⟩).lower ∧ (cell13199 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13199 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13199 ⟨15,by decide⟩).lower ∧ (cell13199 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13199 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13199 ⟨16,by decide⟩).lower ∧ (cell13199 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13199 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13199 ⟨17,by decide⟩).lower ∧ (cell13199 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13199 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13199 ⟨18,by decide⟩).lower ∧ (cell13199 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13199 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13199 ⟨19,by decide⟩).lower ∧ (cell13199 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13199 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13199 ⟨20,by decide⟩).lower ∧ (cell13199 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13199 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13199 ⟨21,by decide⟩).lower ∧ (cell13199 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13199 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13199 ⟨22,by decide⟩).lower ∧ (cell13199 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13199 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13199 ⟨23,by decide⟩).lower ∧ (cell13199 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13199 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13199 ⟨24,by decide⟩).lower ∧ (cell13199 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13199 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13199 ⟨25,by decide⟩).lower ∧ (cell13199 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13199 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13199 ⟨26,by decide⟩).lower ∧ (cell13199 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13199 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13199 ⟨27,by decide⟩).lower ∧ (cell13199 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13199 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13199 ⟨28,by decide⟩).lower ∧ (cell13199 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13199 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13199 ⟨29,by decide⟩).lower ∧ (cell13199 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13199 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13199 ⟨30,by decide⟩).lower ∧ (cell13199 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13199 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13199 ⟨31,by decide⟩).lower ∧ (cell13199 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13199 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13199 ⟨32,by decide⟩).lower ∧ (cell13199 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13199 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13199 ⟨33,by decide⟩).lower ∧ (cell13199 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13199 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13199 ⟨34,by decide⟩).lower ∧ (cell13199 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13199 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13199 ⟨35,by decide⟩).lower ∧ (cell13199 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13199 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13199 ⟨36,by decide⟩).lower ∧ (cell13199 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13199 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13199 ⟨37,by decide⟩).lower ∧ (cell13199 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13199 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13199 ⟨38,by decide⟩).lower ∧ (cell13199 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13199 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13199 ⟨39,by decide⟩).lower ∧ (cell13199 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13199 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13199 ⟨40,by decide⟩).lower ∧ (cell13199 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13199 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13199 ⟨41,by decide⟩).lower ∧ (cell13199 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13199 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13199 ⟨42,by decide⟩).lower ∧ (cell13199 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13199 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13199 ⟨43,by decide⟩).lower ∧ (cell13199 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13199 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13199 ⟨44,by decide⟩).lower ∧ (cell13199 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13199 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13199 ⟨45,by decide⟩).lower ∧ (cell13199 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13199 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13199 ⟨46,by decide⟩).lower ∧ (cell13199 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13199 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13199 ⟨47,by decide⟩).lower ∧ (cell13199 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13199 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13199 ⟨48,by decide⟩).lower ∧ (cell13199 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13199 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13199 ⟨49,by decide⟩).lower ∧ (cell13199 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13199 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13199 ⟨50,by decide⟩).lower ∧ (cell13199 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13199 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13199 ⟨51,by decide⟩).lower ∧ (cell13199 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13199 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13199 ⟨52,by decide⟩).lower ∧ (cell13199 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13199 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13199 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13199 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13199,cell13199,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13199 i).lower ∧
    (cell13199 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13199 i).upper ≤ (0.532 : ℝ) ∧
    (cell13199 i).centre ≤ (0.1 : ℝ) ∧ (cell13199 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13199 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13199 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13199

/-! The local source numeric instances at 13199 have no network premises. -/
namespace BstLean.Part269.N13199
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13199)
open BstLean.Part268 (cell13199)

noncomputable def sourceNumerics13199 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13199 (cell13199 i)
      scalarRow13199.M scalarRow13199.H scalarRow13199.xi := by
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
    energy_allowance := scalarRow13199.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13199]
    centre_nonneg := (scalarRow13199.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D33.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13199])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13199