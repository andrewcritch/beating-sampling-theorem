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
import BstLean.Part269Direction9
import BstLean.Part269Shared9
import BstLean.Part269Finite
import BstLean.Part269Rows9
import BstLean.Part269Source
/-! Actual 12575 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12575
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12575 ≤ (1.035988328417 : ℝ) := by
  have hr : (112.138307460029 : ℝ) ≤ √(12575 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.138307460029 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12575 12575 (11 / 1000) ≤
    (0.008524179536 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12575) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.138307460029 : ℝ) ≤ √(12575 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12575)
  have hdiv : K / √(12575 : ℝ) ≤ K / 112.138307460029 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.138307460029 ≤ (0.008524179536 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12575.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12575 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12575 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12575 := gPlus_lower 12575
end BstLean.Part269.N12575

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12575
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035988328416 : ℝ) ≤ wn 12575 := by
  have hn : √(12575 : ℝ) ≤ 112.138307460030 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12575 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.138307460030 ≤ 2 / √(12575 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254428642 : ℝ) ≤ rhoBar 12575 BstLean.Part154.csC ∧
    rhoBar 12575 BstLean.Part154.csC ≤ 0.000254429036 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035988328416 : ℝ) / (1.295212 * 12575) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035988328417 : ℝ) / (1.29521 * 12575) := by gcongr
      _ ≤ (0.000254429036 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12575 BstLean.Part154.csC) ≤ 0.001017780879 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12575 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12575 BstLean.Part154.csC) (piBar (rhoBar 12575 BstLean.Part154.csC)) ≤ 0.000194334706 ∧
    cc1 (rhoBar 12575 BstLean.Part154.csC) (piBar (rhoBar 12575 BstLean.Part154.csC)) ≤ 0.000123656445 ∧
    cc2 (rhoBar 12575 BstLean.Part154.csC) ≤ 0.000071783491 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12575 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12575 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12575 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12575 BstLean.Part154.csC * nuR (rhoBar 12575 BstLean.Part154.csC)) ≤ 0.000508874256 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254429036 : ℝ) * 0.001017780879 := by gcongr
      _ ≤ (0.000508874256 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12575 BstLean.Part154.csC) * nuR (rhoBar 12575 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001017780879 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12575 BstLean.Part154.csC) * rhoBar 12575 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254429036 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254429036 / 2 + 0.399 * 0.001017780879 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194334706 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508874256 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123656445 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254429036 / 1.414213562 := by gcongr
      _ ≤ (0.000071783491 : ℝ) := by norm_num

end BstLean.Part269.N12575

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12575
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12575 BstLean.Part154.csC) (piBar (rhoBar 12575 BstLean.Part154.csC)) ≤ 1.63093E-7 := by
  have hr0 : 0 ≤ rhoBar 12575 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12575 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12575 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12575 BstLean.Part154.csC) (piBar (rhoBar 12575 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12575 BstLean.Part154.csC) (piBar (rhoBar 12575 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12575 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194334706 : ℝ) ^ 2 + 0.000123656445 ^ 2 + 3 * 0.000071783491 ^ 2 +
        2 * 0.797885 * 0.000194334706 * 0.000123656445 + 2 * 0.000194334706 * 0.000071783491 +
        4 * 0.797885 * 0.000123656445 * 0.000071783491 := by gcongr
    _ ≤ (1.63093E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12575 BstLean.Part154.csC Θ ≤ 0.002656343140 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12575 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12575 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12575 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12575 BstLean.Part154.csC) (piBar (rhoBar 12575 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12575 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035988328417 * 1.63093E-7 / (0.000254428642 : ℝ) := by gcongr
    _ ≤ 0.002656343140 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12575 BstLean.Part154.csC Θ ≤ 0.002947867943 + 0.000671215134 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12575 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12575 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12575 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035988328417 : ℝ) * ((2 * Θ * 0.000254429036 +
        (6863 / 10000) * 0.000254429036 * 12575 * 0.001017780879) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002947867943 + 0.000671215134 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12575 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12575 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12575 0.011 Θ ∧ gammaRatio 12575 0.011 Θ ≤ 0.000087466123 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12575 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035988328417 : ℝ) * 0.525 / ((1 - 0.011) * 12575) := by gcongr
      _ ≤ (0.000087466123 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12575 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12575 0.011 Θ) :=
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
    badAllowance 12575 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12575 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12575 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12575 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12575 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12575 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12575 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12575 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12575 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12575 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12575 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035988328417 : ℝ) * 12575 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12575 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003622837465 + 0.003327558274 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12575

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12575
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12575 BstLean.Part154.csC) (piBar (rhoBar 12575 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12575 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12575 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12575 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12575 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12575 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12575 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12575 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12575 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12575 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12575 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12575 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12575 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12575 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12575 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052747359756 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12575) ≤ 0.010649684378 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12575 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035988328417)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010649684378 + 2 * 0.737676 / 12575) := by gcongr
    _ ≤ (0.052747359756 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12575 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12575

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12575
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497859228 : ℝ) ≤ plow 12575 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12575) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052876405559)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394580149) : eMP 12575 0.011 xi bn ≤ 0.001200422102 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12575 : ℝ) * (1 - 0.011))) ≤ 0.000593532572 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001394580149 / (12575 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593532572 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593532572 : ℝ) + 3.141593 * 0.052876405559 / (12575 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001200422102 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052876405559)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394580149) : PiBarMP 12575 12 0.011 xi bn ≤ 0.162058358914 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12575 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037344077831 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.519841283961 : ℝ) ≤ √((12575 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.138307460029 : ℝ) ≤ √(12575 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12575) ≤ 0.124243076058 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037344077831 + 0.052876405559 * 1.772454 / (2 * (111.519841283961 : ℝ))) * (1 + 0.001200422102) +
        8 / (12575 * 112.138307460029) + 0.124243076058 := by gcongr
    _ ≤ (0.162058358914 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052876405559)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394580149) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282696061773) :
    parallelOracle 12575 0.011 xi bn cd ≤ 0.163058547931 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12575 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12575 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497859228 : ℝ) ≤ plow 12575 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.138307460029 : ℝ) ≤ √(12575 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282696061773 : ℝ) / (2 * 0.560497859228 * 112.138307460029)) * 0.162058358914 +
        0.282696061773 ^ 2 / (2 * 0.560497859228 * 112.138307460029) := by gcongr
    _ ≤ (0.163058547931 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052876405559) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394580149)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282696061773) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12575 12575 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497859228 : ℝ) ≤ plow 12575 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.138307460029 : ℝ) ≤ √(12575 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12575 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12575 Θ 1.22 ≤ 0.011825579769 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.138307460029 := by gcongr <;> linarith
      _ ≤ (0.011825579769 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12575 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12575 12575 0.011 ≤ 0.008524179536 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12575 12575 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12575 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12575 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12575 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12575 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163058547931 + 0.011825579769 + (0.008524179536 : ℝ) *
        (1 + 2 * (0.282696061773 + 0.011825579769) / (0.560497859228 * 112.138307460029))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12575]

end BstLean.Part269.N12575

/-! The original eight local profiles supply actual 12575 moment certificates. -/
namespace BstLean.Part269.N12575
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12575 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12575 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12575 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052876405559 ∧
    0 ≤ bN 12575 BstLean.Part154.csC (groupTheta g) ∧ bN 12575 BstLean.Part154.csC (groupTheta g) ≤ 0.001394580149 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12575 12575 0.011
      (momentAllowance 12575 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12575 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12575 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12575 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12575 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12575 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229948702017 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12575 0.011
      (momentAllowance 12575 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12575 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12575
/-! The actual computed-centre upper energy formula at 12575. -/
namespace BstLean.Part269.N12575
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12575

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12575
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12575)
open BstLean.Part268 (cell12575)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085863633642
  | 2 => 0.086813447414
  | 3 => 0.087762464066
  | 4 => 0.088712344168
  | 5 => 0.089665087835
  | 6 => 0.090623084061
  | 7 => 0.091589164478
  | 8 => 0.092566661568
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12575 12575 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12575 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12575

/-! Actual upper energy certificates on all 43 source endpoints at 12575. -/
namespace BstLean.Part269.N12575
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12575)
open BstLean.Part268 (cell12575)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12575 (gMinus 12575) (1 - (cell12575 i).lower) ≤ 1 ∧
    energyUpper 12575 (gMinus 12575) (BstLean.Part211.gPlus 12575)
      (finiteEnergy 12575 12575 0.011) (1 - (cell12575 i).lower) ≤
      (cell12575 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨10,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨11,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨12,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨13,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨14,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨15,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨16,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨17,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨18,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨19,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨20,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨21,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨22,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨23,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨24,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨25,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨26,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨27,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨28,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨29,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨30,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨31,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨32,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨33,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨34,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨35,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨36,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨37,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨38,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨39,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨40,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨41,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨42,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨43,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨44,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨45,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨46,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨47,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨48,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨49,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨50,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨51,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12575) (by norm_num)
        (q := 1 - (cell12575 ⟨52,by decide⟩).lower)
        (by norm_num [cell12575]) (by norm_num [cell12575])
      exact ⟨E.1,E.2.trans (by norm_num [cell12575])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12575

/-! Source-cell containment and simple scalar guards at 12575. -/
namespace BstLean.Part269.N12575
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12575)
open BstLean.Part268 (cell12575)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12575 ⟨10,by decide⟩).lower ∧ (cell12575 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12575 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12575 ⟨11,by decide⟩).lower ∧ (cell12575 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12575 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12575 ⟨12,by decide⟩).lower ∧ (cell12575 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12575 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12575 ⟨13,by decide⟩).lower ∧ (cell12575 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12575 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12575 ⟨14,by decide⟩).lower ∧ (cell12575 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12575 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12575 ⟨15,by decide⟩).lower ∧ (cell12575 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12575 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12575 ⟨16,by decide⟩).lower ∧ (cell12575 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12575 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12575 ⟨17,by decide⟩).lower ∧ (cell12575 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12575 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12575 ⟨18,by decide⟩).lower ∧ (cell12575 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12575 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12575 ⟨19,by decide⟩).lower ∧ (cell12575 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12575 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12575 ⟨20,by decide⟩).lower ∧ (cell12575 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12575 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12575 ⟨21,by decide⟩).lower ∧ (cell12575 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12575 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12575 ⟨22,by decide⟩).lower ∧ (cell12575 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12575 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12575 ⟨23,by decide⟩).lower ∧ (cell12575 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12575 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12575 ⟨24,by decide⟩).lower ∧ (cell12575 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12575 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12575 ⟨25,by decide⟩).lower ∧ (cell12575 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12575 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12575 ⟨26,by decide⟩).lower ∧ (cell12575 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12575 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12575 ⟨27,by decide⟩).lower ∧ (cell12575 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12575 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12575 ⟨28,by decide⟩).lower ∧ (cell12575 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12575 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12575 ⟨29,by decide⟩).lower ∧ (cell12575 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12575 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12575 ⟨30,by decide⟩).lower ∧ (cell12575 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12575 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12575 ⟨31,by decide⟩).lower ∧ (cell12575 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12575 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12575 ⟨32,by decide⟩).lower ∧ (cell12575 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12575 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12575 ⟨33,by decide⟩).lower ∧ (cell12575 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12575 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12575 ⟨34,by decide⟩).lower ∧ (cell12575 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12575 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12575 ⟨35,by decide⟩).lower ∧ (cell12575 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12575 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12575 ⟨36,by decide⟩).lower ∧ (cell12575 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12575 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12575 ⟨37,by decide⟩).lower ∧ (cell12575 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12575 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12575 ⟨38,by decide⟩).lower ∧ (cell12575 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12575 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12575 ⟨39,by decide⟩).lower ∧ (cell12575 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12575 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12575 ⟨40,by decide⟩).lower ∧ (cell12575 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12575 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12575 ⟨41,by decide⟩).lower ∧ (cell12575 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12575 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12575 ⟨42,by decide⟩).lower ∧ (cell12575 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12575 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12575 ⟨43,by decide⟩).lower ∧ (cell12575 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12575 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12575 ⟨44,by decide⟩).lower ∧ (cell12575 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12575 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12575 ⟨45,by decide⟩).lower ∧ (cell12575 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12575 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12575 ⟨46,by decide⟩).lower ∧ (cell12575 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12575 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12575 ⟨47,by decide⟩).lower ∧ (cell12575 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12575 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12575 ⟨48,by decide⟩).lower ∧ (cell12575 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12575 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12575 ⟨49,by decide⟩).lower ∧ (cell12575 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12575 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12575 ⟨50,by decide⟩).lower ∧ (cell12575 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12575 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12575 ⟨51,by decide⟩).lower ∧ (cell12575 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12575 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12575 ⟨52,by decide⟩).lower ∧ (cell12575 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12575 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12575 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12575 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12575,cell12575,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12575 i).lower ∧
    (cell12575 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12575 i).upper ≤ (0.532 : ℝ) ∧
    (cell12575 i).centre ≤ (0.1 : ℝ) ∧ (cell12575 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12575 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12575 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12575

/-! The local source numeric instances at 12575 have no network premises. -/
namespace BstLean.Part269.N12575
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12575)
open BstLean.Part268 (cell12575)

noncomputable def sourceNumerics12575 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12575 (cell12575 i)
      scalarRow12575.M scalarRow12575.H scalarRow12575.xi := by
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
    energy_allowance := scalarRow12575.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12575]
    centre_nonneg := (scalarRow12575.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12575])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12575
/-! Actual 12576 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12576
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12576 ≤ (1.035986884909 : ℝ) := by
  have hr : (112.142766151009 : ℝ) ≤ √(12576 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.142766151009 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12576 12576 (11 / 1000) ≤
    (0.008523840620 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12576) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.142766151009 : ℝ) ≤ √(12576 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12576)
  have hdiv : K / √(12576 : ℝ) ≤ K / 112.142766151009 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.142766151009 ≤ (0.008523840620 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12576.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12576 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12576 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12576 := gPlus_lower 12576
end BstLean.Part269.N12576

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12576
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035986884908 : ℝ) ≤ wn 12576 := by
  have hn : √(12576 : ℝ) ≤ 112.142766151010 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12576 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.142766151010 ≤ 2 / √(12576 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254408056 : ℝ) ≤ rhoBar 12576 BstLean.Part154.csC ∧
    rhoBar 12576 BstLean.Part154.csC ≤ 0.000254408450 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035986884908 : ℝ) / (1.295212 * 12576) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035986884909 : ℝ) / (1.29521 * 12576) := by gcongr
      _ ≤ (0.000254408450 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12576 BstLean.Part154.csC) ≤ 0.001017698524 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12576 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12576 BstLean.Part154.csC) (piBar (rhoBar 12576 BstLean.Part154.csC)) ≤ 0.000194318981 ∧
    cc1 (rhoBar 12576 BstLean.Part154.csC) (piBar (rhoBar 12576 BstLean.Part154.csC)) ≤ 0.000123646439 ∧
    cc2 (rhoBar 12576 BstLean.Part154.csC) ≤ 0.000071777683 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12576 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12576 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12576 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12576 BstLean.Part154.csC * nuR (rhoBar 12576 BstLean.Part154.csC)) ≤ 0.000508833081 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254408450 : ℝ) * 0.001017698524 := by gcongr
      _ ≤ (0.000508833081 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12576 BstLean.Part154.csC) * nuR (rhoBar 12576 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001017698524 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12576 BstLean.Part154.csC) * rhoBar 12576 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254408450 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254408450 / 2 + 0.399 * 0.001017698524 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194318981 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508833081 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123646439 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254408450 / 1.414213562 := by gcongr
      _ ≤ (0.000071777683 : ℝ) := by norm_num

end BstLean.Part269.N12576

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12576
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12576 BstLean.Part154.csC) (piBar (rhoBar 12576 BstLean.Part154.csC)) ≤ 1.63067E-7 := by
  have hr0 : 0 ≤ rhoBar 12576 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12576 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12576 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12576 BstLean.Part154.csC) (piBar (rhoBar 12576 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12576 BstLean.Part154.csC) (piBar (rhoBar 12576 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12576 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194318981 : ℝ) ^ 2 + 0.000123646439 ^ 2 + 3 * 0.000071777683 ^ 2 +
        2 * 0.797885 * 0.000194318981 * 0.000123646439 + 2 * 0.000194318981 * 0.000071777683 +
        4 * 0.797885 * 0.000123646439 * 0.000071777683 := by gcongr
    _ ≤ (1.63067E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12576 BstLean.Part154.csC Θ ≤ 0.002656130880 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12576 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12576 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12576 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12576 BstLean.Part154.csC) (piBar (rhoBar 12576 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12576 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035986884909 * 1.63067E-7 / (0.000254408056 : ℝ) := by gcongr
    _ ≤ 0.002656130880 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12576 BstLean.Part154.csC Θ ≤ 0.002947621196 + 0.000671159890 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12576 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12576 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12576 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035986884909 : ℝ) * ((2 * Θ * 0.000254408450 +
        (6863 / 10000) * 0.000254408450 * 12576 * 0.001017698524) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002947621196 + 0.000671159890 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12576 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12576 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12576 0.011 Θ ∧ gammaRatio 12576 0.011 Θ ≤ 0.000087459047 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12576 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035986884909 : ℝ) * 0.525 / ((1 - 0.011) * 12576) := by gcongr
      _ ≤ (0.000087459047 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12576 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12576 0.011 Θ) :=
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
    badAllowance 12576 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12576 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12576 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12576 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12576 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12576 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12576 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12576 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12576 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12576 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12576 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035986884909 : ℝ) * 12576 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12576 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003622590718 + 0.003327290770 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12576

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12576
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12576 BstLean.Part154.csC) (piBar (rhoBar 12576 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12576 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12576 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12576 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12576 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12576 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12576 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12576 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12576 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12576 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12576 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12576 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12576 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12576 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12576 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052745239716 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12576) ≤ 0.010649260956 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12576 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035986884909)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010649260956 + 2 * 0.737676 / 12576) := by gcongr
    _ ≤ (0.052745239716 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12576 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12576

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12576
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497905351 : ℝ) ≤ plow 12576 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12576) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052876018373)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394468712) : eMP 12576 0.011 xi bn ≤ 0.001200326321 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12576 : ℝ) * (1 - 0.011))) ≤ 0.000593485261 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001394468712 / (12576 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593485261 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593485261 : ℝ) + 3.141593 * 0.052876018373 / (12576 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001200326321 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052876018373)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394468712) : PiBarMP 12576 12 0.011 xi bn ≤ 0.162051901174 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12576 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037342585771 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.524275384330 : ℝ) ≤ √((12576 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.142766151009 : ℝ) ≤ √(12576 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12576) ≤ 0.124238136270 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037342585771 + 0.052876018373 * 1.772454 / (2 * (111.524275384330 : ℝ))) * (1 + 0.001200326321) +
        8 / (12576 * 112.142766151009) + 0.124238136270 := by gcongr
    _ ≤ (0.162051901174 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052876018373)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394468712) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282693099835) :
    parallelOracle 12576 0.011 xi bn cd ≤ 0.163052018681 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12576 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12576 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497905351 : ℝ) ≤ plow 12576 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.142766151009 : ℝ) ≤ √(12576 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282693099835 : ℝ) / (2 * 0.560497905351 * 112.142766151009)) * 0.162051901174 +
        0.282693099835 ^ 2 / (2 * 0.560497905351 * 112.142766151009) := by gcongr
    _ ≤ (0.163052018681 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052876018373) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394468712)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282693099835) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12576 12576 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497905351 : ℝ) ≤ plow 12576 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.142766151009 : ℝ) ≤ √(12576 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12576 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12576 Θ 1.22 ≤ 0.011825109595 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.142766151009 := by gcongr <;> linarith
      _ ≤ (0.011825109595 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12576 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12576 12576 0.011 ≤ 0.008523840620 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12576 12576 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12576 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12576 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12576 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12576 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163052018681 + 0.011825109595 + (0.008523840620 : ℝ) *
        (1 + 2 * (0.282693099835 + 0.011825109595) / (0.560497905351 * 112.142766151009))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12576]

end BstLean.Part269.N12576

/-! The original eight local profiles supply actual 12576 moment certificates. -/
namespace BstLean.Part269.N12576
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12576 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12576 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12576 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052876018373 ∧
    0 ≤ bN 12576 BstLean.Part154.csC (groupTheta g) ∧ bN 12576 BstLean.Part154.csC (groupTheta g) ≤ 0.001394468712 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12576 12576 0.011
      (momentAllowance 12576 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12576 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12576 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12576 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12576 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12576 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229947860119 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12576 0.011
      (momentAllowance 12576 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12576 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12576
/-! The actual computed-centre upper energy formula at 12576. -/
namespace BstLean.Part269.N12576
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12576

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12576
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12576)
open BstLean.Part268 (cell12576)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085860573412
  | 2 => 0.086810327593
  | 3 => 0.087759275427
  | 4 => 0.088709075397
  | 5 => 0.089661725174
  | 6 => 0.090619610902
  | 7 => 0.091585560909
  | 8 => 0.092562903880
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12576 12576 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12576 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12576

/-! Actual upper energy certificates on all 43 source endpoints at 12576. -/
namespace BstLean.Part269.N12576
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12576)
open BstLean.Part268 (cell12576)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12576 (gMinus 12576) (1 - (cell12576 i).lower) ≤ 1 ∧
    energyUpper 12576 (gMinus 12576) (BstLean.Part211.gPlus 12576)
      (finiteEnergy 12576 12576 0.011) (1 - (cell12576 i).lower) ≤
      (cell12576 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨10,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨11,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨12,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨13,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨14,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨15,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨16,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨17,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨18,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨19,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨20,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨21,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨22,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨23,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨24,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨25,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨26,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨27,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨28,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨29,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨30,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨31,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨32,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨33,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨34,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨35,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨36,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨37,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨38,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨39,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨40,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨41,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨42,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨43,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨44,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨45,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨46,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨47,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨48,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨49,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨50,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨51,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12576) (by norm_num)
        (q := 1 - (cell12576 ⟨52,by decide⟩).lower)
        (by norm_num [cell12576]) (by norm_num [cell12576])
      exact ⟨E.1,E.2.trans (by norm_num [cell12576])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12576

/-! Source-cell containment and simple scalar guards at 12576. -/
namespace BstLean.Part269.N12576
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12576)
open BstLean.Part268 (cell12576)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12576 ⟨10,by decide⟩).lower ∧ (cell12576 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12576 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12576 ⟨11,by decide⟩).lower ∧ (cell12576 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12576 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12576 ⟨12,by decide⟩).lower ∧ (cell12576 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12576 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12576 ⟨13,by decide⟩).lower ∧ (cell12576 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12576 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12576 ⟨14,by decide⟩).lower ∧ (cell12576 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12576 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12576 ⟨15,by decide⟩).lower ∧ (cell12576 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12576 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12576 ⟨16,by decide⟩).lower ∧ (cell12576 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12576 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12576 ⟨17,by decide⟩).lower ∧ (cell12576 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12576 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12576 ⟨18,by decide⟩).lower ∧ (cell12576 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12576 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12576 ⟨19,by decide⟩).lower ∧ (cell12576 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12576 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12576 ⟨20,by decide⟩).lower ∧ (cell12576 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12576 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12576 ⟨21,by decide⟩).lower ∧ (cell12576 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12576 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12576 ⟨22,by decide⟩).lower ∧ (cell12576 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12576 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12576 ⟨23,by decide⟩).lower ∧ (cell12576 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12576 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12576 ⟨24,by decide⟩).lower ∧ (cell12576 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12576 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12576 ⟨25,by decide⟩).lower ∧ (cell12576 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12576 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12576 ⟨26,by decide⟩).lower ∧ (cell12576 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12576 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12576 ⟨27,by decide⟩).lower ∧ (cell12576 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12576 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12576 ⟨28,by decide⟩).lower ∧ (cell12576 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12576 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12576 ⟨29,by decide⟩).lower ∧ (cell12576 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12576 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12576 ⟨30,by decide⟩).lower ∧ (cell12576 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12576 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12576 ⟨31,by decide⟩).lower ∧ (cell12576 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12576 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12576 ⟨32,by decide⟩).lower ∧ (cell12576 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12576 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12576 ⟨33,by decide⟩).lower ∧ (cell12576 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12576 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12576 ⟨34,by decide⟩).lower ∧ (cell12576 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12576 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12576 ⟨35,by decide⟩).lower ∧ (cell12576 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12576 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12576 ⟨36,by decide⟩).lower ∧ (cell12576 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12576 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12576 ⟨37,by decide⟩).lower ∧ (cell12576 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12576 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12576 ⟨38,by decide⟩).lower ∧ (cell12576 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12576 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12576 ⟨39,by decide⟩).lower ∧ (cell12576 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12576 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12576 ⟨40,by decide⟩).lower ∧ (cell12576 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12576 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12576 ⟨41,by decide⟩).lower ∧ (cell12576 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12576 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12576 ⟨42,by decide⟩).lower ∧ (cell12576 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12576 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12576 ⟨43,by decide⟩).lower ∧ (cell12576 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12576 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12576 ⟨44,by decide⟩).lower ∧ (cell12576 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12576 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12576 ⟨45,by decide⟩).lower ∧ (cell12576 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12576 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12576 ⟨46,by decide⟩).lower ∧ (cell12576 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12576 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12576 ⟨47,by decide⟩).lower ∧ (cell12576 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12576 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12576 ⟨48,by decide⟩).lower ∧ (cell12576 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12576 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12576 ⟨49,by decide⟩).lower ∧ (cell12576 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12576 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12576 ⟨50,by decide⟩).lower ∧ (cell12576 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12576 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12576 ⟨51,by decide⟩).lower ∧ (cell12576 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12576 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12576 ⟨52,by decide⟩).lower ∧ (cell12576 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12576 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12576 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12576 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12576,cell12576,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12576 i).lower ∧
    (cell12576 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12576 i).upper ≤ (0.532 : ℝ) ∧
    (cell12576 i).centre ≤ (0.1 : ℝ) ∧ (cell12576 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12576 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12576 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12576

/-! The local source numeric instances at 12576 have no network premises. -/
namespace BstLean.Part269.N12576
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12576)
open BstLean.Part268 (cell12576)

noncomputable def sourceNumerics12576 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12576 (cell12576 i)
      scalarRow12576.M scalarRow12576.H scalarRow12576.xi := by
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
    energy_allowance := scalarRow12576.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12576]
    centre_nonneg := (scalarRow12576.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12576])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12576
/-! Actual 12577 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12577
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12577 ≤ (1.035985441573 : ℝ) := by
  have hr : (112.147224664723 : ℝ) ≤ √(12577 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.147224664723 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12577 12577 (11 / 1000) ≤
    (0.008523501744 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12577) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.147224664723 : ℝ) ≤ √(12577 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12577)
  have hdiv : K / √(12577 : ℝ) ≤ K / 112.147224664723 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.147224664723 ≤ (0.008523501744 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12577.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12577 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12577 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12577 := gPlus_lower 12577
end BstLean.Part269.N12577

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12577
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035985441572 : ℝ) ≤ wn 12577 := by
  have hn : √(12577 : ℝ) ≤ 112.147224664724 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12577 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.147224664724 ≤ 2 / √(12577 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254387474 : ℝ) ≤ rhoBar 12577 BstLean.Part154.csC ∧
    rhoBar 12577 BstLean.Part154.csC ≤ 0.000254387868 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035985441572 : ℝ) / (1.295212 * 12577) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035985441573 : ℝ) / (1.29521 * 12577) := by gcongr
      _ ≤ (0.000254387868 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12577 BstLean.Part154.csC) ≤ 0.001017616186 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12577 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12577 BstLean.Part154.csC) (piBar (rhoBar 12577 BstLean.Part154.csC)) ≤ 0.000194303260 ∧
    cc1 (rhoBar 12577 BstLean.Part154.csC) (piBar (rhoBar 12577 BstLean.Part154.csC)) ≤ 0.000123636436 ∧
    cc2 (rhoBar 12577 BstLean.Part154.csC) ≤ 0.000071771876 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12577 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12577 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12577 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12577 BstLean.Part154.csC * nuR (rhoBar 12577 BstLean.Part154.csC)) ≤ 0.000508791915 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254387868 : ℝ) * 0.001017616186 := by gcongr
      _ ≤ (0.000508791915 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12577 BstLean.Part154.csC) * nuR (rhoBar 12577 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001017616186 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12577 BstLean.Part154.csC) * rhoBar 12577 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254387868 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254387868 / 2 + 0.399 * 0.001017616186 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194303260 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508791915 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123636436 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254387868 / 1.414213562 := by gcongr
      _ ≤ (0.000071771876 : ℝ) := by norm_num

end BstLean.Part269.N12577

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12577
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12577 BstLean.Part154.csC) (piBar (rhoBar 12577 BstLean.Part154.csC)) ≤ 1.63040E-7 := by
  have hr0 : 0 ≤ rhoBar 12577 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12577 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12577 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12577 BstLean.Part154.csC) (piBar (rhoBar 12577 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12577 BstLean.Part154.csC) (piBar (rhoBar 12577 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12577 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194303260 : ℝ) ^ 2 + 0.000123636436 ^ 2 + 3 * 0.000071771876 ^ 2 +
        2 * 0.797885 * 0.000194303260 * 0.000123636436 + 2 * 0.000194303260 * 0.000071771876 +
        4 * 0.797885 * 0.000123636436 * 0.000071771876 := by gcongr
    _ ≤ (1.63040E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12577 BstLean.Part154.csC Θ ≤ 0.002655902254 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12577 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12577 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12577 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12577 BstLean.Part154.csC) (piBar (rhoBar 12577 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12577 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035985441573 * 1.63040E-7 / (0.000254387474 : ℝ) := by gcongr
    _ ≤ 0.002655902254 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12577 BstLean.Part154.csC Θ ≤ 0.002947374508 + 0.000671104658 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12577 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12577 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12577 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035985441573 : ℝ) * ((2 * Θ * 0.000254387868 +
        (6863 / 10000) * 0.000254387868 * 12577 * 0.001017616186) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002947374508 + 0.000671104658 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12577 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12577 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12577 0.011 Θ ∧ gammaRatio 12577 0.011 Θ ≤ 0.000087451971 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12577 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035985441573 : ℝ) * 0.525 / ((1 - 0.011) * 12577) := by gcongr
      _ ≤ (0.000087451971 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12577 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12577 0.011 Θ) :=
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
    badAllowance 12577 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12577 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12577 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12577 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12577 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12577 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12577 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12577 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12577 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12577 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12577 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035985441573 : ℝ) * 12577 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12577 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003622344030 + 0.003327006912 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12577

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12577
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12577 BstLean.Part154.csC) (piBar (rhoBar 12577 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12577 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12577 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12577 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12577 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12577 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12577 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12577 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12577 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12577 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12577 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12577 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12577 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12577 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12577 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052743119934 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12577) ≤ 0.010648837585 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12577 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035985441573)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010648837585 + 2 * 0.737676 / 12577) := by gcongr
    _ ≤ (0.052743119934 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12577 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12577

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12577
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497951466 : ℝ) ≤ plow 12577 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12577) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052875622659)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394348684) : eMP 12577 0.011 xi bn ≤ 0.001200226887 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12577 : ℝ) * (1 - 0.011))) ≤ 0.000593436125 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001394348684 / (12577 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593436125 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593436125 : ℝ) + 3.141593 * 0.052875622659 / (12577 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001200226887 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052875622659)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394348684) : PiBarMP 12577 12 0.011 xi bn ≤ 0.162045328588 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12577 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037340978616 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.528709308410 : ℝ) ≤ √((12577 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.147224664723 : ℝ) ≤ √(12577 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12577) ≤ 0.124233197072 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037340978616 + 0.052875622659 * 1.772454 / (2 * (111.528709308410 : ℝ))) * (1 + 0.001200226887) +
        8 / (12577 * 112.147224664723) + 0.124233197072 := by gcongr
    _ ≤ (0.162045328588 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052875622659)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394348684) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282690119608) :
    parallelOracle 12577 0.011 xi bn cd ≤ 0.163045374228 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12577 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12577 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497951466 : ℝ) ≤ plow 12577 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.147224664723 : ℝ) ≤ √(12577 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282690119608 : ℝ) / (2 * 0.560497951466 * 112.147224664723)) * 0.162045328588 +
        0.282690119608 ^ 2 / (2 * 0.560497951466 * 112.147224664723) := by gcongr
    _ ≤ (0.163045374228 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052875622659) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394348684)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282690119608) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12577 12577 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497951466 : ℝ) ≤ plow 12577 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.147224664723 : ℝ) ≤ √(12577 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12577 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12577 Θ 1.22 ≤ 0.011824639477 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.147224664723 := by gcongr <;> linarith
      _ ≤ (0.011824639477 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12577 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12577 12577 0.011 ≤ 0.008523501744 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12577 12577 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12577 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12577 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12577 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12577 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163045374228 + 0.011824639477 + (0.008523501744 : ℝ) *
        (1 + 2 * (0.282690119608 + 0.011824639477) / (0.560497951466 * 112.147224664723))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12577]

end BstLean.Part269.N12577

/-! The original eight local profiles supply actual 12577 moment certificates. -/
namespace BstLean.Part269.N12577
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12577 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12577 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12577 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052875622659 ∧
    0 ≤ bN 12577 BstLean.Part154.csC (groupTheta g) ∧ bN 12577 BstLean.Part154.csC (groupTheta g) ≤ 0.001394348684 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12577 12577 0.011
      (momentAllowance 12577 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12577 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12577 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12577 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12577 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12577 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229946999674 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12577 0.011
      (momentAllowance 12577 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12577 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12577
/-! The actual computed-centre upper energy formula at 12577. -/
namespace BstLean.Part269.N12577
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12577

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12577
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12577)
open BstLean.Part268 (cell12577)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085857514414
  | 2 => 0.086807209056
  | 3 => 0.087756088136
  | 4 => 0.088705808054
  | 5 => 0.089658364038
  | 6 => 0.090616139384
  | 7 => 0.091581959124
  | 8 => 0.092559148146
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12577 12577 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12577 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12577

/-! Actual upper energy certificates on all 43 source endpoints at 12577. -/
namespace BstLean.Part269.N12577
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12577)
open BstLean.Part268 (cell12577)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12577 (gMinus 12577) (1 - (cell12577 i).lower) ≤ 1 ∧
    energyUpper 12577 (gMinus 12577) (BstLean.Part211.gPlus 12577)
      (finiteEnergy 12577 12577 0.011) (1 - (cell12577 i).lower) ≤
      (cell12577 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨10,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨11,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨12,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨13,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨14,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨15,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨16,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨17,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨18,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨19,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨20,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨21,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨22,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨23,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨24,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨25,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨26,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨27,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨28,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨29,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨30,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨31,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨32,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨33,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨34,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨35,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨36,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨37,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨38,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨39,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨40,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨41,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨42,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨43,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨44,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨45,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨46,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨47,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨48,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨49,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨50,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨51,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12577) (by norm_num)
        (q := 1 - (cell12577 ⟨52,by decide⟩).lower)
        (by norm_num [cell12577]) (by norm_num [cell12577])
      exact ⟨E.1,E.2.trans (by norm_num [cell12577])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12577

/-! Source-cell containment and simple scalar guards at 12577. -/
namespace BstLean.Part269.N12577
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12577)
open BstLean.Part268 (cell12577)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12577 ⟨10,by decide⟩).lower ∧ (cell12577 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12577 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12577 ⟨11,by decide⟩).lower ∧ (cell12577 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12577 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12577 ⟨12,by decide⟩).lower ∧ (cell12577 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12577 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12577 ⟨13,by decide⟩).lower ∧ (cell12577 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12577 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12577 ⟨14,by decide⟩).lower ∧ (cell12577 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12577 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12577 ⟨15,by decide⟩).lower ∧ (cell12577 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12577 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12577 ⟨16,by decide⟩).lower ∧ (cell12577 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12577 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12577 ⟨17,by decide⟩).lower ∧ (cell12577 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12577 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12577 ⟨18,by decide⟩).lower ∧ (cell12577 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12577 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12577 ⟨19,by decide⟩).lower ∧ (cell12577 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12577 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12577 ⟨20,by decide⟩).lower ∧ (cell12577 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12577 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12577 ⟨21,by decide⟩).lower ∧ (cell12577 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12577 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12577 ⟨22,by decide⟩).lower ∧ (cell12577 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12577 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12577 ⟨23,by decide⟩).lower ∧ (cell12577 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12577 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12577 ⟨24,by decide⟩).lower ∧ (cell12577 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12577 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12577 ⟨25,by decide⟩).lower ∧ (cell12577 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12577 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12577 ⟨26,by decide⟩).lower ∧ (cell12577 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12577 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12577 ⟨27,by decide⟩).lower ∧ (cell12577 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12577 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12577 ⟨28,by decide⟩).lower ∧ (cell12577 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12577 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12577 ⟨29,by decide⟩).lower ∧ (cell12577 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12577 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12577 ⟨30,by decide⟩).lower ∧ (cell12577 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12577 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12577 ⟨31,by decide⟩).lower ∧ (cell12577 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12577 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12577 ⟨32,by decide⟩).lower ∧ (cell12577 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12577 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12577 ⟨33,by decide⟩).lower ∧ (cell12577 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12577 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12577 ⟨34,by decide⟩).lower ∧ (cell12577 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12577 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12577 ⟨35,by decide⟩).lower ∧ (cell12577 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12577 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12577 ⟨36,by decide⟩).lower ∧ (cell12577 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12577 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12577 ⟨37,by decide⟩).lower ∧ (cell12577 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12577 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12577 ⟨38,by decide⟩).lower ∧ (cell12577 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12577 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12577 ⟨39,by decide⟩).lower ∧ (cell12577 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12577 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12577 ⟨40,by decide⟩).lower ∧ (cell12577 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12577 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12577 ⟨41,by decide⟩).lower ∧ (cell12577 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12577 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12577 ⟨42,by decide⟩).lower ∧ (cell12577 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12577 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12577 ⟨43,by decide⟩).lower ∧ (cell12577 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12577 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12577 ⟨44,by decide⟩).lower ∧ (cell12577 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12577 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12577 ⟨45,by decide⟩).lower ∧ (cell12577 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12577 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12577 ⟨46,by decide⟩).lower ∧ (cell12577 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12577 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12577 ⟨47,by decide⟩).lower ∧ (cell12577 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12577 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12577 ⟨48,by decide⟩).lower ∧ (cell12577 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12577 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12577 ⟨49,by decide⟩).lower ∧ (cell12577 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12577 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12577 ⟨50,by decide⟩).lower ∧ (cell12577 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12577 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12577 ⟨51,by decide⟩).lower ∧ (cell12577 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12577 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12577 ⟨52,by decide⟩).lower ∧ (cell12577 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12577 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12577 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12577 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12577,cell12577,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12577 i).lower ∧
    (cell12577 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12577 i).upper ≤ (0.532 : ℝ) ∧
    (cell12577 i).centre ≤ (0.1 : ℝ) ∧ (cell12577 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12577 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12577 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12577

/-! The local source numeric instances at 12577 have no network premises. -/
namespace BstLean.Part269.N12577
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12577)
open BstLean.Part268 (cell12577)

noncomputable def sourceNumerics12577 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12577 (cell12577 i)
      scalarRow12577.M scalarRow12577.H scalarRow12577.xi := by
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
    energy_allowance := scalarRow12577.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12577]
    centre_nonneg := (scalarRow12577.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12577])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12577
/-! Actual 12578 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12578
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12578 ≤ (1.035983998411 : ℝ) := by
  have hr : (112.151683001192 : ℝ) ≤ √(12578 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.151683001192 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12578 12578 (11 / 1000) ≤
    (0.008523162909 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12578) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.151683001192 : ℝ) ≤ √(12578 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12578)
  have hdiv : K / √(12578 : ℝ) ≤ K / 112.151683001192 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.151683001192 ≤ (0.008523162909 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12578.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12578 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12578 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12578 := gPlus_lower 12578
end BstLean.Part269.N12578

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12578
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035983998410 : ℝ) ≤ wn 12578 := by
  have hn : √(12578 : ℝ) ≤ 112.151683001193 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12578 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.151683001193 ≤ 2 / √(12578 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254366895 : ℝ) ≤ rhoBar 12578 BstLean.Part154.csC ∧
    rhoBar 12578 BstLean.Part154.csC ≤ 0.000254367288 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035983998410 : ℝ) / (1.295212 * 12578) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035983998411 : ℝ) / (1.29521 * 12578) := by gcongr
      _ ≤ (0.000254367288 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12578 BstLean.Part154.csC) ≤ 0.001017533855 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12578 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12578 BstLean.Part154.csC) (piBar (rhoBar 12578 BstLean.Part154.csC)) ≤ 0.000194287540 ∧
    cc1 (rhoBar 12578 BstLean.Part154.csC) (piBar (rhoBar 12578 BstLean.Part154.csC)) ≤ 0.000123626433 ∧
    cc2 (rhoBar 12578 BstLean.Part154.csC) ≤ 0.000071766069 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12578 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12578 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12578 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12578 BstLean.Part154.csC * nuR (rhoBar 12578 BstLean.Part154.csC)) ≤ 0.000508750752 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254367288 : ℝ) * 0.001017533855 := by gcongr
      _ ≤ (0.000508750752 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12578 BstLean.Part154.csC) * nuR (rhoBar 12578 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001017533855 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12578 BstLean.Part154.csC) * rhoBar 12578 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254367288 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254367288 / 2 + 0.399 * 0.001017533855 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194287540 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508750752 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123626433 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254367288 / 1.414213562 := by gcongr
      _ ≤ (0.000071766069 : ℝ) := by norm_num

end BstLean.Part269.N12578

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12578
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12578 BstLean.Part154.csC) (piBar (rhoBar 12578 BstLean.Part154.csC)) ≤ 1.63014E-7 := by
  have hr0 : 0 ≤ rhoBar 12578 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12578 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12578 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12578 BstLean.Part154.csC) (piBar (rhoBar 12578 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12578 BstLean.Part154.csC) (piBar (rhoBar 12578 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12578 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194287540 : ℝ) ^ 2 + 0.000123626433 ^ 2 + 3 * 0.000071766069 ^ 2 +
        2 * 0.797885 * 0.000194287540 * 0.000123626433 + 2 * 0.000194287540 * 0.000071766069 +
        4 * 0.797885 * 0.000123626433 * 0.000071766069 := by gcongr
    _ ≤ (1.63014E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12578 BstLean.Part154.csC Θ ≤ 0.002655689854 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12578 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12578 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12578 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12578 BstLean.Part154.csC) (piBar (rhoBar 12578 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12578 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035983998411 * 1.63014E-7 / (0.000254366895 : ℝ) := by gcongr
    _ ≤ 0.002655689854 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12578 BstLean.Part154.csC Θ ≤ 0.002947127828 + 0.000671049430 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12578 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12578 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12578 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035983998411 : ℝ) * ((2 * Θ * 0.000254367288 +
        (6863 / 10000) * 0.000254367288 * 12578 * 0.001017533855) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002947127828 + 0.000671049430 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12578 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12578 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12578 0.011 Θ ∧ gammaRatio 12578 0.011 Θ ≤ 0.000087444896 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12578 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035983998411 : ℝ) * 0.525 / ((1 - 0.011) * 12578) := by gcongr
      _ ≤ (0.000087444896 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12578 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12578 0.011 Θ) :=
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
    badAllowance 12578 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12578 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12578 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12578 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12578 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12578 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12578 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12578 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12578 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12578 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12578 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035983998411 : ℝ) * 12578 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12578 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003622097350 + 0.003326739284 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12578

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12578
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12578 BstLean.Part154.csC) (piBar (rhoBar 12578 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12578 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12578 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12578 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12578 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12578 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12578 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12578 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12578 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12578 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12578 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12578 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12578 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12578 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12578 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052741000409 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12578) ≤ 0.010648414265 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12578 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035983998411)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010648414265 + 2 * 0.737676 / 12578) := by gcongr
    _ ≤ (0.052741000409 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12578 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12578

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12578
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560497997575 : ℝ) ≤ plow 12578 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12578) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052875235475)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394237174) : eMP 12578 0.011 xi bn ≤ 0.001200131087 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12578 : ℝ) * (1 - 0.011))) ≤ 0.000593388805 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001394237174 / (12578 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593388805 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593388805 : ℝ) + 3.141593 * 0.052875235475 / (12578 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001200131087 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052875235475)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394237174) : PiBarMP 12578 12 0.011 xi bn ≤ 0.162038870928 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12578 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037339485455 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.533143056223 : ℝ) ≤ √((12578 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.151683001192 : ℝ) ≤ √(12578 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12578) ≤ 0.124228258462 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037339485455 + 0.052875235475 * 1.772454 / (2 * (111.533143056223 : ℝ))) * (1 + 0.001200131087) +
        8 / (12578 * 112.151683001192) + 0.124228258462 := by gcongr
    _ ≤ (0.162038870928 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052875235475)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394237174) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282687158183) :
    parallelOracle 12578 0.011 xi bn cd ≤ 0.163038845077 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12578 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12578 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560497997575 : ℝ) ≤ plow 12578 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.151683001192 : ℝ) ≤ √(12578 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282687158183 : ℝ) / (2 * 0.560497997575 * 112.151683001192)) * 0.162038870928 +
        0.282687158183 ^ 2 / (2 * 0.560497997575 * 112.151683001192) := by gcongr
    _ ≤ (0.163038845077 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052875235475) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394237174)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282687158183) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12578 12578 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560497997575 : ℝ) ≤ plow 12578 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.151683001192 : ℝ) ≤ √(12578 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12578 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12578 Θ 1.22 ≤ 0.011824169416 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.151683001192 := by gcongr <;> linarith
      _ ≤ (0.011824169416 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12578 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12578 12578 0.011 ≤ 0.008523162909 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12578 12578 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12578 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12578 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12578 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12578 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163038845077 + 0.011824169416 + (0.008523162909 : ℝ) *
        (1 + 2 * (0.282687158183 + 0.011824169416) / (0.560497997575 * 112.151683001192))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12578]

end BstLean.Part269.N12578

/-! The original eight local profiles supply actual 12578 moment certificates. -/
namespace BstLean.Part269.N12578
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12578 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12578 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12578 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052875235475 ∧
    0 ≤ bN 12578 BstLean.Part154.csC (groupTheta g) ∧ bN 12578 BstLean.Part154.csC (groupTheta g) ≤ 0.001394237174 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12578 12578 0.011
      (momentAllowance 12578 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12578 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12578 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12578 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12578 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12578 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229946157774 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12578 0.011
      (momentAllowance 12578 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12578 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12578
/-! The actual computed-centre upper energy formula at 12578. -/
namespace BstLean.Part269.N12578
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12578

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12578
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12578)
open BstLean.Part268 (cell12578)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085854456646
  | 2 => 0.086804091801
  | 3 => 0.087752902192
  | 4 => 0.088702542137
  | 5 => 0.089655004425
  | 6 => 0.090612669506
  | 7 => 0.091578359121
  | 8 => 0.092555394365
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12578 12578 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12578 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12578

/-! Actual upper energy certificates on all 43 source endpoints at 12578. -/
namespace BstLean.Part269.N12578
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12578)
open BstLean.Part268 (cell12578)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12578 (gMinus 12578) (1 - (cell12578 i).lower) ≤ 1 ∧
    energyUpper 12578 (gMinus 12578) (BstLean.Part211.gPlus 12578)
      (finiteEnergy 12578 12578 0.011) (1 - (cell12578 i).lower) ≤
      (cell12578 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨10,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨11,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨12,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨13,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨14,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨15,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨16,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨17,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨18,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨19,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨20,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨21,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨22,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨23,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨24,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨25,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨26,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨27,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨28,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨29,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨30,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨31,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨32,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨33,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨34,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨35,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨36,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨37,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨38,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨39,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨40,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨41,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨42,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨43,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨44,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨45,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨46,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨47,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨48,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨49,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨50,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨51,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12578) (by norm_num)
        (q := 1 - (cell12578 ⟨52,by decide⟩).lower)
        (by norm_num [cell12578]) (by norm_num [cell12578])
      exact ⟨E.1,E.2.trans (by norm_num [cell12578])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12578

/-! Source-cell containment and simple scalar guards at 12578. -/
namespace BstLean.Part269.N12578
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12578)
open BstLean.Part268 (cell12578)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12578 ⟨10,by decide⟩).lower ∧ (cell12578 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12578 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12578 ⟨11,by decide⟩).lower ∧ (cell12578 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12578 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12578 ⟨12,by decide⟩).lower ∧ (cell12578 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12578 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12578 ⟨13,by decide⟩).lower ∧ (cell12578 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12578 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12578 ⟨14,by decide⟩).lower ∧ (cell12578 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12578 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12578 ⟨15,by decide⟩).lower ∧ (cell12578 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12578 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12578 ⟨16,by decide⟩).lower ∧ (cell12578 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12578 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12578 ⟨17,by decide⟩).lower ∧ (cell12578 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12578 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12578 ⟨18,by decide⟩).lower ∧ (cell12578 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12578 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12578 ⟨19,by decide⟩).lower ∧ (cell12578 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12578 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12578 ⟨20,by decide⟩).lower ∧ (cell12578 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12578 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12578 ⟨21,by decide⟩).lower ∧ (cell12578 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12578 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12578 ⟨22,by decide⟩).lower ∧ (cell12578 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12578 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12578 ⟨23,by decide⟩).lower ∧ (cell12578 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12578 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12578 ⟨24,by decide⟩).lower ∧ (cell12578 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12578 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12578 ⟨25,by decide⟩).lower ∧ (cell12578 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12578 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12578 ⟨26,by decide⟩).lower ∧ (cell12578 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12578 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12578 ⟨27,by decide⟩).lower ∧ (cell12578 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12578 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12578 ⟨28,by decide⟩).lower ∧ (cell12578 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12578 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12578 ⟨29,by decide⟩).lower ∧ (cell12578 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12578 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12578 ⟨30,by decide⟩).lower ∧ (cell12578 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12578 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12578 ⟨31,by decide⟩).lower ∧ (cell12578 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12578 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12578 ⟨32,by decide⟩).lower ∧ (cell12578 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12578 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12578 ⟨33,by decide⟩).lower ∧ (cell12578 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12578 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12578 ⟨34,by decide⟩).lower ∧ (cell12578 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12578 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12578 ⟨35,by decide⟩).lower ∧ (cell12578 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12578 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12578 ⟨36,by decide⟩).lower ∧ (cell12578 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12578 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12578 ⟨37,by decide⟩).lower ∧ (cell12578 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12578 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12578 ⟨38,by decide⟩).lower ∧ (cell12578 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12578 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12578 ⟨39,by decide⟩).lower ∧ (cell12578 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12578 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12578 ⟨40,by decide⟩).lower ∧ (cell12578 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12578 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12578 ⟨41,by decide⟩).lower ∧ (cell12578 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12578 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12578 ⟨42,by decide⟩).lower ∧ (cell12578 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12578 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12578 ⟨43,by decide⟩).lower ∧ (cell12578 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12578 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12578 ⟨44,by decide⟩).lower ∧ (cell12578 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12578 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12578 ⟨45,by decide⟩).lower ∧ (cell12578 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12578 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12578 ⟨46,by decide⟩).lower ∧ (cell12578 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12578 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12578 ⟨47,by decide⟩).lower ∧ (cell12578 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12578 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12578 ⟨48,by decide⟩).lower ∧ (cell12578 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12578 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12578 ⟨49,by decide⟩).lower ∧ (cell12578 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12578 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12578 ⟨50,by decide⟩).lower ∧ (cell12578 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12578 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12578 ⟨51,by decide⟩).lower ∧ (cell12578 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12578 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12578 ⟨52,by decide⟩).lower ∧ (cell12578 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12578 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12578 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12578 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12578,cell12578,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12578 i).lower ∧
    (cell12578 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12578 i).upper ≤ (0.532 : ℝ) ∧
    (cell12578 i).centre ≤ (0.1 : ℝ) ∧ (cell12578 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12578 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12578 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12578

/-! The local source numeric instances at 12578 have no network premises. -/
namespace BstLean.Part269.N12578
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12578)
open BstLean.Part268 (cell12578)

noncomputable def sourceNumerics12578 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12578 (cell12578 i)
      scalarRow12578.M scalarRow12578.H scalarRow12578.xi := by
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
    energy_allowance := scalarRow12578.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12578]
    centre_nonneg := (scalarRow12578.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12578])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12578
/-! Actual 12579 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12579
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12579 ≤ (1.035982555422 : ℝ) := by
  have hr : (112.156141160437 : ℝ) ≤ √(12579 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.156141160437 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12579 12579 (11 / 1000) ≤
    (0.008522824114 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12579) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.156141160437 : ℝ) ≤ √(12579 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12579)
  have hdiv : K / √(12579 : ℝ) ≤ K / 112.156141160437 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.156141160437 ≤ (0.008522824114 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12579.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12579 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12579 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12579 := gPlus_lower 12579
end BstLean.Part269.N12579

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12579
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035982555421 : ℝ) ≤ wn 12579 := by
  have hn : √(12579 : ℝ) ≤ 112.156141160438 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12579 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.156141160438 ≤ 2 / √(12579 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254346319 : ℝ) ≤ rhoBar 12579 BstLean.Part154.csC ∧
    rhoBar 12579 BstLean.Part154.csC ≤ 0.000254346713 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035982555421 : ℝ) / (1.295212 * 12579) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035982555422 : ℝ) / (1.29521 * 12579) := by gcongr
      _ ≤ (0.000254346713 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12579 BstLean.Part154.csC) ≤ 0.001017451545 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12579 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12579 BstLean.Part154.csC) (piBar (rhoBar 12579 BstLean.Part154.csC)) ≤ 0.000194271824 ∧
    cc1 (rhoBar 12579 BstLean.Part154.csC) (piBar (rhoBar 12579 BstLean.Part154.csC)) ≤ 0.000123616433 ∧
    cc2 (rhoBar 12579 BstLean.Part154.csC) ≤ 0.000071760264 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12579 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12579 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12579 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12579 BstLean.Part154.csC * nuR (rhoBar 12579 BstLean.Part154.csC)) ≤ 0.000508709599 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254346713 : ℝ) * 0.001017451545 := by gcongr
      _ ≤ (0.000508709599 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12579 BstLean.Part154.csC) * nuR (rhoBar 12579 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001017451545 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12579 BstLean.Part154.csC) * rhoBar 12579 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254346713 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254346713 / 2 + 0.399 * 0.001017451545 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194271824 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508709599 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123616433 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254346713 / 1.414213562 := by gcongr
      _ ≤ (0.000071760264 : ℝ) := by norm_num

end BstLean.Part269.N12579

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12579
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12579 BstLean.Part154.csC) (piBar (rhoBar 12579 BstLean.Part154.csC)) ≤ 1.62988E-7 := by
  have hr0 : 0 ≤ rhoBar 12579 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12579 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12579 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12579 BstLean.Part154.csC) (piBar (rhoBar 12579 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12579 BstLean.Part154.csC) (piBar (rhoBar 12579 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12579 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194271824 : ℝ) ^ 2 + 0.000123616433 ^ 2 + 3 * 0.000071760264 ^ 2 +
        2 * 0.797885 * 0.000194271824 * 0.000123616433 + 2 * 0.000194271824 * 0.000071760264 +
        4 * 0.797885 * 0.000123616433 * 0.000071760264 := by gcongr
    _ ≤ (1.62988E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12579 BstLean.Part154.csC Θ ≤ 0.002655477389 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12579 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12579 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12579 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12579 BstLean.Part154.csC) (piBar (rhoBar 12579 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12579 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035982555422 * 1.62988E-7 / (0.000254346319 : ℝ) := by gcongr
    _ ≤ 0.002655477389 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12579 BstLean.Part154.csC Θ ≤ 0.002946881231 + 0.000670994217 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12579 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12579 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12579 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035982555422 : ℝ) * ((2 * Θ * 0.000254346713 +
        (6863 / 10000) * 0.000254346713 * 12579 * 0.001017451545) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002946881231 + 0.000670994217 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12579 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12579 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12579 0.011 Θ ∧ gammaRatio 12579 0.011 Θ ≤ 0.000087437823 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12579 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035982555422 : ℝ) * 0.525 / ((1 - 0.011) * 12579) := by gcongr
      _ ≤ (0.000087437823 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12579 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12579 0.011 Θ) :=
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
    badAllowance 12579 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12579 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12579 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12579 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12579 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12579 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12579 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12579 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12579 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12579 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12579 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035982555422 : ℝ) * 12579 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12579 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003621850753 + 0.003326471606 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12579

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12579
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12579 BstLean.Part154.csC) (piBar (rhoBar 12579 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12579 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12579 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12579 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12579 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12579 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12579 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12579 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12579 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12579 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12579 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12579 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12579 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12579 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12579 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052738881136 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12579) ≤ 0.010647990995 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12579 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035982555422)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010647990995 + 2 * 0.737676 / 12579) := by gcongr
    _ ≤ (0.052738881136 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12579 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12579

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12579
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498043675 : ℝ) ≤ plow 12579 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12579) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052874848347)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394125630) : eMP 12579 0.011 xi bn ≤ 0.001200035282 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12579 : ℝ) * (1 - 0.011))) ≤ 0.000593341482 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001394125630 / (12579 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593341482 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593341482 : ℝ) + 3.141593 * 0.052874848347 / (12579 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001200035282 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052874848347)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394125630) : PiBarMP 12579 12 0.011 xi bn ≤ 0.162032413344 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12579 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037337991778 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.537576627789 : ℝ) ≤ √((12579 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.156141160437 : ℝ) ≤ √(12579 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12579) ≤ 0.124223320441 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037337991778 + 0.052874848347 * 1.772454 / (2 * (111.537576627789 : ℝ))) * (1 + 0.001200035282) +
        8 / (12579 * 112.156141160437) + 0.124223320441 := by gcongr
    _ ≤ (0.162032413344 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052874848347)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394125630) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282684197129) :
    parallelOracle 12579 0.011 xi bn cd ≤ 0.163032316011 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12579 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12579 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498043675 : ℝ) ≤ plow 12579 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.156141160437 : ℝ) ≤ √(12579 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282684197129 : ℝ) / (2 * 0.560498043675 * 112.156141160437)) * 0.162032413344 +
        0.282684197129 ^ 2 / (2 * 0.560498043675 * 112.156141160437) := by gcongr
    _ ≤ (0.163032316011 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052874848347) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394125630)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282684197129) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12579 12579 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498043675 : ℝ) ≤ plow 12579 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.156141160437 : ℝ) ≤ √(12579 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12579 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12579 Θ 1.22 ≤ 0.011823699410 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.156141160437 := by gcongr <;> linarith
      _ ≤ (0.011823699410 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12579 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12579 12579 0.011 ≤ 0.008522824114 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12579 12579 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12579 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12579 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12579 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12579 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163032316011 + 0.011823699410 + (0.008522824114 : ℝ) *
        (1 + 2 * (0.282684197129 + 0.011823699410) / (0.560498043675 * 112.156141160437))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12579]

end BstLean.Part269.N12579

/-! The original eight local profiles supply actual 12579 moment certificates. -/
namespace BstLean.Part269.N12579
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12579 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12579 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12579 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052874848347 ∧
    0 ≤ bN 12579 BstLean.Part154.csC (groupTheta g) ∧ bN 12579 BstLean.Part154.csC (groupTheta g) ≤ 0.001394125630 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12579 12579 0.011
      (momentAllowance 12579 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12579 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12579 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12579 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12579 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12579 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229945315993 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12579 0.011
      (momentAllowance 12579 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12579 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12579
/-! The actual computed-centre upper energy formula at 12579. -/
namespace BstLean.Part269.N12579
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12579

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12579
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12579)
open BstLean.Part268 (cell12579)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085851400107
  | 2 => 0.086800975828
  | 3 => 0.087749717593
  | 4 => 0.088699277645
  | 5 => 0.089651646333
  | 6 => 0.090609201267
  | 7 => 0.091574760897
  | 8 => 0.092551642533
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12579 12579 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12579 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12579

/-! Actual upper energy certificates on all 43 source endpoints at 12579. -/
namespace BstLean.Part269.N12579
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12579)
open BstLean.Part268 (cell12579)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12579 (gMinus 12579) (1 - (cell12579 i).lower) ≤ 1 ∧
    energyUpper 12579 (gMinus 12579) (BstLean.Part211.gPlus 12579)
      (finiteEnergy 12579 12579 0.011) (1 - (cell12579 i).lower) ≤
      (cell12579 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨10,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨11,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨12,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨13,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨14,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨15,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨16,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨17,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨18,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨19,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨20,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨21,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨22,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨23,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨24,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨25,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨26,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨27,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨28,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨29,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨30,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨31,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨32,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨33,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨34,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨35,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨36,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨37,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨38,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨39,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨40,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨41,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨42,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨43,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨44,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨45,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨46,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨47,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨48,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨49,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨50,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨51,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12579) (by norm_num)
        (q := 1 - (cell12579 ⟨52,by decide⟩).lower)
        (by norm_num [cell12579]) (by norm_num [cell12579])
      exact ⟨E.1,E.2.trans (by norm_num [cell12579])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12579

/-! Source-cell containment and simple scalar guards at 12579. -/
namespace BstLean.Part269.N12579
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12579)
open BstLean.Part268 (cell12579)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12579 ⟨10,by decide⟩).lower ∧ (cell12579 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12579 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12579 ⟨11,by decide⟩).lower ∧ (cell12579 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12579 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12579 ⟨12,by decide⟩).lower ∧ (cell12579 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12579 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12579 ⟨13,by decide⟩).lower ∧ (cell12579 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12579 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12579 ⟨14,by decide⟩).lower ∧ (cell12579 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12579 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12579 ⟨15,by decide⟩).lower ∧ (cell12579 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12579 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12579 ⟨16,by decide⟩).lower ∧ (cell12579 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12579 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12579 ⟨17,by decide⟩).lower ∧ (cell12579 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12579 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12579 ⟨18,by decide⟩).lower ∧ (cell12579 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12579 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12579 ⟨19,by decide⟩).lower ∧ (cell12579 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12579 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12579 ⟨20,by decide⟩).lower ∧ (cell12579 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12579 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12579 ⟨21,by decide⟩).lower ∧ (cell12579 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12579 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12579 ⟨22,by decide⟩).lower ∧ (cell12579 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12579 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12579 ⟨23,by decide⟩).lower ∧ (cell12579 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12579 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12579 ⟨24,by decide⟩).lower ∧ (cell12579 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12579 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12579 ⟨25,by decide⟩).lower ∧ (cell12579 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12579 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12579 ⟨26,by decide⟩).lower ∧ (cell12579 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12579 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12579 ⟨27,by decide⟩).lower ∧ (cell12579 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12579 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12579 ⟨28,by decide⟩).lower ∧ (cell12579 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12579 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12579 ⟨29,by decide⟩).lower ∧ (cell12579 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12579 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12579 ⟨30,by decide⟩).lower ∧ (cell12579 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12579 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12579 ⟨31,by decide⟩).lower ∧ (cell12579 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12579 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12579 ⟨32,by decide⟩).lower ∧ (cell12579 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12579 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12579 ⟨33,by decide⟩).lower ∧ (cell12579 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12579 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12579 ⟨34,by decide⟩).lower ∧ (cell12579 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12579 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12579 ⟨35,by decide⟩).lower ∧ (cell12579 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12579 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12579 ⟨36,by decide⟩).lower ∧ (cell12579 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12579 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12579 ⟨37,by decide⟩).lower ∧ (cell12579 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12579 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12579 ⟨38,by decide⟩).lower ∧ (cell12579 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12579 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12579 ⟨39,by decide⟩).lower ∧ (cell12579 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12579 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12579 ⟨40,by decide⟩).lower ∧ (cell12579 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12579 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12579 ⟨41,by decide⟩).lower ∧ (cell12579 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12579 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12579 ⟨42,by decide⟩).lower ∧ (cell12579 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12579 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12579 ⟨43,by decide⟩).lower ∧ (cell12579 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12579 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12579 ⟨44,by decide⟩).lower ∧ (cell12579 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12579 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12579 ⟨45,by decide⟩).lower ∧ (cell12579 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12579 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12579 ⟨46,by decide⟩).lower ∧ (cell12579 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12579 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12579 ⟨47,by decide⟩).lower ∧ (cell12579 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12579 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12579 ⟨48,by decide⟩).lower ∧ (cell12579 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12579 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12579 ⟨49,by decide⟩).lower ∧ (cell12579 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12579 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12579 ⟨50,by decide⟩).lower ∧ (cell12579 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12579 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12579 ⟨51,by decide⟩).lower ∧ (cell12579 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12579 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12579 ⟨52,by decide⟩).lower ∧ (cell12579 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12579 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12579 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12579 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12579,cell12579,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12579 i).lower ∧
    (cell12579 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12579 i).upper ≤ (0.532 : ℝ) ∧
    (cell12579 i).centre ≤ (0.1 : ℝ) ∧ (cell12579 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12579 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12579 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12579

/-! The local source numeric instances at 12579 have no network premises. -/
namespace BstLean.Part269.N12579
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12579)
open BstLean.Part268 (cell12579)

noncomputable def sourceNumerics12579 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12579 (cell12579 i)
      scalarRow12579.M scalarRow12579.H scalarRow12579.xi := by
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
    energy_allowance := scalarRow12579.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12579]
    centre_nonneg := (scalarRow12579.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12579])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12579
/-! Actual 12580 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12580
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12580 ≤ (1.035981112605 : ℝ) := by
  have hr : (112.160599142479 : ℝ) ≤ √(12580 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.160599142479 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12580 12580 (11 / 1000) ≤
    (0.008522485360 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12580) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.160599142479 : ℝ) ≤ √(12580 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12580)
  have hdiv : K / √(12580 : ℝ) ≤ K / 112.160599142479 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.160599142479 ≤ (0.008522485360 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12580.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12580 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12580 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12580 := gPlus_lower 12580
end BstLean.Part269.N12580

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12580
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035981112604 : ℝ) ≤ wn 12580 := by
  have hn : √(12580 : ℝ) ≤ 112.160599142480 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12580 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.160599142480 ≤ 2 / √(12580 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254325746 : ℝ) ≤ rhoBar 12580 BstLean.Part154.csC ∧
    rhoBar 12580 BstLean.Part154.csC ≤ 0.000254326140 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035981112604 : ℝ) / (1.295212 * 12580) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035981112605 : ℝ) / (1.29521 * 12580) := by gcongr
      _ ≤ (0.000254326140 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12580 BstLean.Part154.csC) ≤ 0.001017369242 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12580 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12580 BstLean.Part154.csC) (piBar (rhoBar 12580 BstLean.Part154.csC)) ≤ 0.000194256109 ∧
    cc1 (rhoBar 12580 BstLean.Part154.csC) (piBar (rhoBar 12580 BstLean.Part154.csC)) ≤ 0.000123606434 ∧
    cc2 (rhoBar 12580 BstLean.Part154.csC) ≤ 0.000071754460 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12580 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12580 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12580 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12580 BstLean.Part154.csC * nuR (rhoBar 12580 BstLean.Part154.csC)) ≤ 0.000508668451 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254326140 : ℝ) * 0.001017369242 := by gcongr
      _ ≤ (0.000508668451 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12580 BstLean.Part154.csC) * nuR (rhoBar 12580 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001017369242 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12580 BstLean.Part154.csC) * rhoBar 12580 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254326140 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254326140 / 2 + 0.399 * 0.001017369242 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194256109 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508668451 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123606434 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254326140 / 1.414213562 := by gcongr
      _ ≤ (0.000071754460 : ℝ) := by norm_num

end BstLean.Part269.N12580

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12580
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12580 BstLean.Part154.csC) (piBar (rhoBar 12580 BstLean.Part154.csC)) ≤ 1.62961E-7 := by
  have hr0 : 0 ≤ rhoBar 12580 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12580 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12580 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12580 BstLean.Part154.csC) (piBar (rhoBar 12580 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12580 BstLean.Part154.csC) (piBar (rhoBar 12580 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12580 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194256109 : ℝ) ^ 2 + 0.000123606434 ^ 2 + 3 * 0.000071754460 ^ 2 +
        2 * 0.797885 * 0.000194256109 * 0.000123606434 + 2 * 0.000194256109 * 0.000071754460 +
        4 * 0.797885 * 0.000123606434 * 0.000071754460 := by gcongr
    _ ≤ (1.62961E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12580 BstLean.Part154.csC Θ ≤ 0.002655248567 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12580 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12580 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12580 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12580 BstLean.Part154.csC) (piBar (rhoBar 12580 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12580 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035981112605 * 1.62961E-7 / (0.000254325746 : ℝ) := by gcongr
    _ ≤ 0.002655248567 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12580 BstLean.Part154.csC Θ ≤ 0.002946634641 + 0.000670939008 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12580 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12580 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12580 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035981112605 : ℝ) * ((2 * Θ * 0.000254326140 +
        (6863 / 10000) * 0.000254326140 * 12580 * 0.001017369242) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002946634641 + 0.000670939008 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12580 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12580 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12580 0.011 Θ ∧ gammaRatio 12580 0.011 Θ ≤ 0.000087430751 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12580 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035981112605 : ℝ) * 0.525 / ((1 - 0.011) * 12580) := by gcongr
      _ ≤ (0.000087430751 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12580 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12580 0.011 Θ) :=
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
    badAllowance 12580 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12580 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12580 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12580 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12580 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12580 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12580 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12580 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12580 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12580 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12580 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035981112605 : ℝ) * 12580 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12580 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003621604163 + 0.003326187575 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12580

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12580
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12580 BstLean.Part154.csC) (piBar (rhoBar 12580 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12580 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12580 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12580 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12580 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12580 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12580 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12580 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12580 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12580 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12580 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12580 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12580 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12580 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12580 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052736762115 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12580) ≤ 0.010647567775 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12580 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035981112605)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010647567775 + 2 * 0.737676 / 12580) := by gcongr
    _ ≤ (0.052736762115 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12580 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12580

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12580
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498089769 : ℝ) ≤ plow 12580 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12580) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052874452640)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394005498) : eMP 12580 0.011 xi bn ≤ 0.001199935827 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12580 : ℝ) * (1 - 0.011))) ≤ 0.000593292335 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001394005498 / (12580 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593292335 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593292335 : ℝ) + 3.141593 * 0.052874452640 / (12580 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001199935827 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052874452640)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394005498) : PiBarMP 12580 12 0.011 xi bn ≤ 0.162025840940 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12580 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037336383034 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.542010023129 : ℝ) ≤ √((12580 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.160599142479 : ℝ) ≤ √(12580 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12580) ≤ 0.124218383009 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037336383034 + 0.052874452640 * 1.772454 / (2 * (111.542010023129 : ℝ))) * (1 + 0.001199935827) +
        8 / (12580 * 112.160599142479) + 0.124218383009 := by gcongr
    _ ≤ (0.162025840940 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052874452640)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394005498) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282681217669) :
    parallelOracle 12580 0.011 xi bn cd ≤ 0.163025671768 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12580 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12580 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498089769 : ℝ) ≤ plow 12580 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.160599142479 : ℝ) ≤ √(12580 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282681217669 : ℝ) / (2 * 0.560498089769 * 112.160599142479)) * 0.162025840940 +
        0.282681217669 ^ 2 / (2 * 0.560498089769 * 112.160599142479) := by gcongr
    _ ≤ (0.163025671768 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052874452640) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001394005498)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282681217669) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12580 12580 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498089769 : ℝ) ≤ plow 12580 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.160599142479 : ℝ) ≤ √(12580 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12580 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12580 Θ 1.22 ≤ 0.011823229460 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.160599142479 := by gcongr <;> linarith
      _ ≤ (0.011823229460 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12580 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12580 12580 0.011 ≤ 0.008522485360 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12580 12580 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12580 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12580 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12580 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12580 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163025671768 + 0.011823229460 + (0.008522485360 : ℝ) *
        (1 + 2 * (0.282681217669 + 0.011823229460) / (0.560498089769 * 112.160599142479))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12580]

end BstLean.Part269.N12580

/-! The original eight local profiles supply actual 12580 moment certificates. -/
namespace BstLean.Part269.N12580
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12580 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12580 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12580 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052874452640 ∧
    0 ≤ bN 12580 BstLean.Part154.csC (groupTheta g) ∧ bN 12580 BstLean.Part154.csC (groupTheta g) ≤ 0.001394005498 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12580 12580 0.011
      (momentAllowance 12580 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12580 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12580 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12580 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12580 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12580 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229944455554 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12580 0.011
      (momentAllowance 12580 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12580 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12580
/-! The actual computed-centre upper energy formula at 12580. -/
namespace BstLean.Part269.N12580
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12580

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12580
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12580)
open BstLean.Part268 (cell12580)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085848344796
  | 2 => 0.086797861134
  | 3 => 0.087746534339
  | 4 => 0.088696014576
  | 5 => 0.089648289760
  | 6 => 0.090605734664
  | 7 => 0.091571164452
  | 8 => 0.092547892649
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12580 12580 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12580 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12580

/-! Actual upper energy certificates on all 43 source endpoints at 12580. -/
namespace BstLean.Part269.N12580
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12580)
open BstLean.Part268 (cell12580)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12580 (gMinus 12580) (1 - (cell12580 i).lower) ≤ 1 ∧
    energyUpper 12580 (gMinus 12580) (BstLean.Part211.gPlus 12580)
      (finiteEnergy 12580 12580 0.011) (1 - (cell12580 i).lower) ≤
      (cell12580 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨10,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨11,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨12,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨13,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨14,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨15,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨16,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨17,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨18,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨19,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨20,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨21,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨22,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨23,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨24,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨25,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨26,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨27,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨28,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨29,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨30,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨31,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨32,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨33,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨34,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨35,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨36,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨37,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨38,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨39,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨40,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨41,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨42,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨43,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨44,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨45,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨46,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨47,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨48,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨49,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨50,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨51,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12580) (by norm_num)
        (q := 1 - (cell12580 ⟨52,by decide⟩).lower)
        (by norm_num [cell12580]) (by norm_num [cell12580])
      exact ⟨E.1,E.2.trans (by norm_num [cell12580])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12580

/-! Source-cell containment and simple scalar guards at 12580. -/
namespace BstLean.Part269.N12580
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12580)
open BstLean.Part268 (cell12580)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12580 ⟨10,by decide⟩).lower ∧ (cell12580 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12580 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12580 ⟨11,by decide⟩).lower ∧ (cell12580 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12580 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12580 ⟨12,by decide⟩).lower ∧ (cell12580 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12580 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12580 ⟨13,by decide⟩).lower ∧ (cell12580 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12580 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12580 ⟨14,by decide⟩).lower ∧ (cell12580 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12580 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12580 ⟨15,by decide⟩).lower ∧ (cell12580 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12580 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12580 ⟨16,by decide⟩).lower ∧ (cell12580 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12580 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12580 ⟨17,by decide⟩).lower ∧ (cell12580 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12580 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12580 ⟨18,by decide⟩).lower ∧ (cell12580 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12580 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12580 ⟨19,by decide⟩).lower ∧ (cell12580 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12580 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12580 ⟨20,by decide⟩).lower ∧ (cell12580 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12580 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12580 ⟨21,by decide⟩).lower ∧ (cell12580 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12580 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12580 ⟨22,by decide⟩).lower ∧ (cell12580 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12580 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12580 ⟨23,by decide⟩).lower ∧ (cell12580 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12580 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12580 ⟨24,by decide⟩).lower ∧ (cell12580 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12580 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12580 ⟨25,by decide⟩).lower ∧ (cell12580 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12580 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12580 ⟨26,by decide⟩).lower ∧ (cell12580 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12580 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12580 ⟨27,by decide⟩).lower ∧ (cell12580 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12580 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12580 ⟨28,by decide⟩).lower ∧ (cell12580 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12580 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12580 ⟨29,by decide⟩).lower ∧ (cell12580 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12580 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12580 ⟨30,by decide⟩).lower ∧ (cell12580 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12580 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12580 ⟨31,by decide⟩).lower ∧ (cell12580 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12580 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12580 ⟨32,by decide⟩).lower ∧ (cell12580 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12580 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12580 ⟨33,by decide⟩).lower ∧ (cell12580 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12580 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12580 ⟨34,by decide⟩).lower ∧ (cell12580 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12580 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12580 ⟨35,by decide⟩).lower ∧ (cell12580 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12580 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12580 ⟨36,by decide⟩).lower ∧ (cell12580 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12580 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12580 ⟨37,by decide⟩).lower ∧ (cell12580 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12580 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12580 ⟨38,by decide⟩).lower ∧ (cell12580 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12580 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12580 ⟨39,by decide⟩).lower ∧ (cell12580 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12580 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12580 ⟨40,by decide⟩).lower ∧ (cell12580 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12580 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12580 ⟨41,by decide⟩).lower ∧ (cell12580 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12580 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12580 ⟨42,by decide⟩).lower ∧ (cell12580 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12580 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12580 ⟨43,by decide⟩).lower ∧ (cell12580 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12580 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12580 ⟨44,by decide⟩).lower ∧ (cell12580 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12580 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12580 ⟨45,by decide⟩).lower ∧ (cell12580 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12580 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12580 ⟨46,by decide⟩).lower ∧ (cell12580 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12580 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12580 ⟨47,by decide⟩).lower ∧ (cell12580 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12580 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12580 ⟨48,by decide⟩).lower ∧ (cell12580 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12580 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12580 ⟨49,by decide⟩).lower ∧ (cell12580 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12580 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12580 ⟨50,by decide⟩).lower ∧ (cell12580 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12580 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12580 ⟨51,by decide⟩).lower ∧ (cell12580 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12580 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12580 ⟨52,by decide⟩).lower ∧ (cell12580 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12580 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12580 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12580 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12580,cell12580,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12580 i).lower ∧
    (cell12580 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12580 i).upper ≤ (0.532 : ℝ) ∧
    (cell12580 i).centre ≤ (0.1 : ℝ) ∧ (cell12580 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12580 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12580 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12580

/-! The local source numeric instances at 12580 have no network premises. -/
namespace BstLean.Part269.N12580
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12580)
open BstLean.Part268 (cell12580)

noncomputable def sourceNumerics12580 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12580 (cell12580 i)
      scalarRow12580.M scalarRow12580.H scalarRow12580.xi := by
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
    energy_allowance := scalarRow12580.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12580]
    centre_nonneg := (scalarRow12580.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12580])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12580
/-! Actual 12581 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12581
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12581 ≤ (1.035979669962 : ℝ) := by
  have hr : (112.165056947339 : ℝ) ≤ √(12581 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.165056947339 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12581 12581 (11 / 1000) ≤
    (0.008522146646 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12581) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.165056947339 : ℝ) ≤ √(12581 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12581)
  have hdiv : K / √(12581 : ℝ) ≤ K / 112.165056947339 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.165056947339 ≤ (0.008522146646 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12581.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12581 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12581 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12581 := gPlus_lower 12581
end BstLean.Part269.N12581

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12581
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035979669961 : ℝ) ≤ wn 12581 := by
  have hn : √(12581 : ℝ) ≤ 112.165056947340 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12581 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.165056947340 ≤ 2 / √(12581 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254305177 : ℝ) ≤ rhoBar 12581 BstLean.Part154.csC ∧
    rhoBar 12581 BstLean.Part154.csC ≤ 0.000254305571 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035979669961 : ℝ) / (1.295212 * 12581) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035979669962 : ℝ) / (1.29521 * 12581) := by gcongr
      _ ≤ (0.000254305571 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12581 BstLean.Part154.csC) ≤ 0.001017286956 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12581 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12581 BstLean.Part154.csC) (piBar (rhoBar 12581 BstLean.Part154.csC)) ≤ 0.000194240398 ∧
    cc1 (rhoBar 12581 BstLean.Part154.csC) (piBar (rhoBar 12581 BstLean.Part154.csC)) ≤ 0.000123596437 ∧
    cc2 (rhoBar 12581 BstLean.Part154.csC) ≤ 0.000071748657 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12581 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12581 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12581 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12581 BstLean.Part154.csC * nuR (rhoBar 12581 BstLean.Part154.csC)) ≤ 0.000508627310 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254305571 : ℝ) * 0.001017286956 := by gcongr
      _ ≤ (0.000508627310 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12581 BstLean.Part154.csC) * nuR (rhoBar 12581 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001017286956 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12581 BstLean.Part154.csC) * rhoBar 12581 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254305571 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254305571 / 2 + 0.399 * 0.001017286956 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194240398 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508627310 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123596437 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254305571 / 1.414213562 := by gcongr
      _ ≤ (0.000071748657 : ℝ) := by norm_num

end BstLean.Part269.N12581

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12581
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12581 BstLean.Part154.csC) (piBar (rhoBar 12581 BstLean.Part154.csC)) ≤ 1.62935E-7 := by
  have hr0 : 0 ≤ rhoBar 12581 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12581 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12581 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12581 BstLean.Part154.csC) (piBar (rhoBar 12581 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12581 BstLean.Part154.csC) (piBar (rhoBar 12581 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12581 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194240398 : ℝ) ^ 2 + 0.000123596437 ^ 2 + 3 * 0.000071748657 ^ 2 +
        2 * 0.797885 * 0.000194240398 * 0.000123596437 + 2 * 0.000194240398 * 0.000071748657 +
        4 * 0.797885 * 0.000123596437 * 0.000071748657 := by gcongr
    _ ≤ (1.62935E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12581 BstLean.Part154.csC Θ ≤ 0.002655035962 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12581 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12581 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12581 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12581 BstLean.Part154.csC) (piBar (rhoBar 12581 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12581 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035979669962 * 1.62935E-7 / (0.000254305177 : ℝ) := by gcongr
    _ ≤ 0.002655035962 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12581 BstLean.Part154.csC Θ ≤ 0.002946388110 + 0.000670883811 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12581 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12581 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12581 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035979669962 : ℝ) * ((2 * Θ * 0.000254305571 +
        (6863 / 10000) * 0.000254305571 * 12581 * 0.001017286956) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002946388110 + 0.000670883811 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12581 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12581 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12581 0.011 Θ ∧ gammaRatio 12581 0.011 Θ ≤ 0.000087423679 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12581 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035979669962 : ℝ) * 0.525 / ((1 - 0.011) * 12581) := by gcongr
      _ ≤ (0.000087423679 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12581 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12581 0.011 Θ) :=
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
    badAllowance 12581 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12581 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12581 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12581 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12581 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12581 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12581 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12581 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12581 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12581 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12581 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035979669962 : ℝ) * 12581 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12581 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003621357632 + 0.003325919773 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12581

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12581
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12581 BstLean.Part154.csC) (piBar (rhoBar 12581 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12581 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12581 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12581 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12581 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12581 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12581 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12581 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12581 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12581 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12581 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12581 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12581 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12581 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12581 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052734643351 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12581) ≤ 0.010647144606 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12581 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035979669962)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010647144606 + 2 * 0.737676 / 12581) := by gcongr
    _ ≤ (0.052734643351 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12581 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12581

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12581
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498135855 : ℝ) ≤ plow 12581 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12581) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052874065513)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393893881) : eMP 12581 0.011 xi bn ≤ 0.001199840006 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12581 : ℝ) * (1 - 0.011))) ≤ 0.000593245004 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001393893881 / (12581 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593245004 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593245004 : ℝ) + 3.141593 * 0.052874065513 / (12581 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001199840006 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052874065513)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393893881) : PiBarMP 12581 12 0.011 xi bn ≤ 0.162019383435 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12581 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037334888255 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.546443242265 : ℝ) ≤ √((12581 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.165056947339 : ℝ) ≤ √(12581 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12581) ≤ 0.124213446166 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037334888255 + 0.052874065513 * 1.772454 / (2 * (111.546443242265 : ℝ))) * (1 + 0.001199840006) +
        8 / (12581 * 112.165056947339) + 0.124213446166 := by gcongr
    _ ≤ (0.162019383435 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052874065513)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393893881) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282678257120) :
    parallelOracle 12581 0.011 xi bn cd ≤ 0.163019142800 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12581 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12581 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498135855 : ℝ) ≤ plow 12581 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.165056947339 : ℝ) ≤ √(12581 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282678257120 : ℝ) / (2 * 0.560498135855 * 112.165056947339)) * 0.162019383435 +
        0.282678257120 ^ 2 / (2 * 0.560498135855 * 112.165056947339) := by gcongr
    _ ≤ (0.163019142800 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052874065513) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393893881)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282678257120) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12581 12581 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498135855 : ℝ) ≤ plow 12581 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.165056947339 : ℝ) ≤ √(12581 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12581 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12581 Θ 1.22 ≤ 0.011822759567 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.165056947339 := by gcongr <;> linarith
      _ ≤ (0.011822759567 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12581 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12581 12581 0.011 ≤ 0.008522146646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12581 12581 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12581 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12581 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12581 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12581 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163019142800 + 0.011822759567 + (0.008522146646 : ℝ) *
        (1 + 2 * (0.282678257120 + 0.011822759567) / (0.560498135855 * 112.165056947339))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12581]

end BstLean.Part269.N12581

/-! The original eight local profiles supply actual 12581 moment certificates. -/
namespace BstLean.Part269.N12581
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12581 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12581 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12581 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052874065513 ∧
    0 ≤ bN 12581 BstLean.Part154.csC (groupTheta g) ∧ bN 12581 BstLean.Part154.csC (groupTheta g) ≤ 0.001393893881 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12581 12581 0.011
      (momentAllowance 12581 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12581 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12581 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12581 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12581 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12581 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229943613769 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12581 0.011
      (momentAllowance 12581 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12581 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12581
/-! The actual computed-centre upper energy formula at 12581. -/
namespace BstLean.Part269.N12581
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12581

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12581
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12581)
open BstLean.Part268 (cell12581)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085845290711
  | 2 => 0.086794747719
  | 3 => 0.087743352427
  | 4 => 0.088692752928
  | 5 => 0.089644934705
  | 6 => 0.090602269696
  | 7 => 0.091567569782
  | 8 => 0.092544144710
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12581 12581 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12581 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12581

/-! Actual upper energy certificates on all 43 source endpoints at 12581. -/
namespace BstLean.Part269.N12581
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12581)
open BstLean.Part268 (cell12581)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12581 (gMinus 12581) (1 - (cell12581 i).lower) ≤ 1 ∧
    energyUpper 12581 (gMinus 12581) (BstLean.Part211.gPlus 12581)
      (finiteEnergy 12581 12581 0.011) (1 - (cell12581 i).lower) ≤
      (cell12581 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨10,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨11,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨12,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨13,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨14,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨15,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨16,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨17,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨18,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨19,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨20,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨21,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨22,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨23,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨24,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨25,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨26,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨27,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨28,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨29,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨30,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨31,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨32,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨33,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨34,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨35,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨36,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨37,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨38,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨39,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨40,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨41,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨42,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨43,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨44,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨45,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨46,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨47,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨48,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨49,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨50,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨51,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12581) (by norm_num)
        (q := 1 - (cell12581 ⟨52,by decide⟩).lower)
        (by norm_num [cell12581]) (by norm_num [cell12581])
      exact ⟨E.1,E.2.trans (by norm_num [cell12581])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12581

/-! Source-cell containment and simple scalar guards at 12581. -/
namespace BstLean.Part269.N12581
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12581)
open BstLean.Part268 (cell12581)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12581 ⟨10,by decide⟩).lower ∧ (cell12581 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12581 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12581 ⟨11,by decide⟩).lower ∧ (cell12581 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12581 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12581 ⟨12,by decide⟩).lower ∧ (cell12581 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12581 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12581 ⟨13,by decide⟩).lower ∧ (cell12581 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12581 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12581 ⟨14,by decide⟩).lower ∧ (cell12581 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12581 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12581 ⟨15,by decide⟩).lower ∧ (cell12581 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12581 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12581 ⟨16,by decide⟩).lower ∧ (cell12581 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12581 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12581 ⟨17,by decide⟩).lower ∧ (cell12581 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12581 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12581 ⟨18,by decide⟩).lower ∧ (cell12581 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12581 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12581 ⟨19,by decide⟩).lower ∧ (cell12581 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12581 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12581 ⟨20,by decide⟩).lower ∧ (cell12581 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12581 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12581 ⟨21,by decide⟩).lower ∧ (cell12581 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12581 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12581 ⟨22,by decide⟩).lower ∧ (cell12581 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12581 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12581 ⟨23,by decide⟩).lower ∧ (cell12581 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12581 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12581 ⟨24,by decide⟩).lower ∧ (cell12581 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12581 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12581 ⟨25,by decide⟩).lower ∧ (cell12581 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12581 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12581 ⟨26,by decide⟩).lower ∧ (cell12581 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12581 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12581 ⟨27,by decide⟩).lower ∧ (cell12581 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12581 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12581 ⟨28,by decide⟩).lower ∧ (cell12581 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12581 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12581 ⟨29,by decide⟩).lower ∧ (cell12581 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12581 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12581 ⟨30,by decide⟩).lower ∧ (cell12581 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12581 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12581 ⟨31,by decide⟩).lower ∧ (cell12581 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12581 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12581 ⟨32,by decide⟩).lower ∧ (cell12581 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12581 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12581 ⟨33,by decide⟩).lower ∧ (cell12581 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12581 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12581 ⟨34,by decide⟩).lower ∧ (cell12581 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12581 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12581 ⟨35,by decide⟩).lower ∧ (cell12581 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12581 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12581 ⟨36,by decide⟩).lower ∧ (cell12581 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12581 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12581 ⟨37,by decide⟩).lower ∧ (cell12581 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12581 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12581 ⟨38,by decide⟩).lower ∧ (cell12581 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12581 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12581 ⟨39,by decide⟩).lower ∧ (cell12581 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12581 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12581 ⟨40,by decide⟩).lower ∧ (cell12581 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12581 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12581 ⟨41,by decide⟩).lower ∧ (cell12581 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12581 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12581 ⟨42,by decide⟩).lower ∧ (cell12581 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12581 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12581 ⟨43,by decide⟩).lower ∧ (cell12581 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12581 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12581 ⟨44,by decide⟩).lower ∧ (cell12581 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12581 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12581 ⟨45,by decide⟩).lower ∧ (cell12581 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12581 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12581 ⟨46,by decide⟩).lower ∧ (cell12581 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12581 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12581 ⟨47,by decide⟩).lower ∧ (cell12581 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12581 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12581 ⟨48,by decide⟩).lower ∧ (cell12581 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12581 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12581 ⟨49,by decide⟩).lower ∧ (cell12581 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12581 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12581 ⟨50,by decide⟩).lower ∧ (cell12581 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12581 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12581 ⟨51,by decide⟩).lower ∧ (cell12581 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12581 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12581 ⟨52,by decide⟩).lower ∧ (cell12581 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12581 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12581 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12581 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12581,cell12581,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12581 i).lower ∧
    (cell12581 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12581 i).upper ≤ (0.532 : ℝ) ∧
    (cell12581 i).centre ≤ (0.1 : ℝ) ∧ (cell12581 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12581 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12581 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12581

/-! The local source numeric instances at 12581 have no network premises. -/
namespace BstLean.Part269.N12581
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12581)
open BstLean.Part268 (cell12581)

noncomputable def sourceNumerics12581 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12581 (cell12581 i)
      scalarRow12581.M scalarRow12581.H scalarRow12581.xi := by
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
    energy_allowance := scalarRow12581.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12581]
    centre_nonneg := (scalarRow12581.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12581])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12581
/-! Actual 12582 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12582
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12582 ≤ (1.035978227492 : ℝ) := by
  have hr : (112.169514575039 : ℝ) ≤ √(12582 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.169514575039 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12582 12582 (11 / 1000) ≤
    (0.008521807973 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12582) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.169514575039 : ℝ) ≤ √(12582 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12582)
  have hdiv : K / √(12582 : ℝ) ≤ K / 112.169514575039 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.169514575039 ≤ (0.008521807973 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12582.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12582 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12582 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12582 := gPlus_lower 12582
end BstLean.Part269.N12582

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12582
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035978227491 : ℝ) ≤ wn 12582 := by
  have hn : √(12582 : ℝ) ≤ 112.169514575040 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12582 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.169514575040 ≤ 2 / √(12582 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254284611 : ℝ) ≤ rhoBar 12582 BstLean.Part154.csC ∧
    rhoBar 12582 BstLean.Part154.csC ≤ 0.000254285005 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035978227491 : ℝ) / (1.295212 * 12582) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035978227492 : ℝ) / (1.29521 * 12582) := by gcongr
      _ ≤ (0.000254285005 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12582 BstLean.Part154.csC) ≤ 0.001017204681 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12582 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12582 BstLean.Part154.csC) (piBar (rhoBar 12582 BstLean.Part154.csC)) ≤ 0.000194224688 ∧
    cc1 (rhoBar 12582 BstLean.Part154.csC) (piBar (rhoBar 12582 BstLean.Part154.csC)) ≤ 0.000123586441 ∧
    cc2 (rhoBar 12582 BstLean.Part154.csC) ≤ 0.000071742854 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12582 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12582 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12582 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12582 BstLean.Part154.csC * nuR (rhoBar 12582 BstLean.Part154.csC)) ≤ 0.000508586175 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254285005 : ℝ) * 0.001017204681 := by gcongr
      _ ≤ (0.000508586175 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12582 BstLean.Part154.csC) * nuR (rhoBar 12582 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001017204681 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12582 BstLean.Part154.csC) * rhoBar 12582 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254285005 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254285005 / 2 + 0.399 * 0.001017204681 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194224688 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508586175 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123586441 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254285005 / 1.414213562 := by gcongr
      _ ≤ (0.000071742854 : ℝ) := by norm_num

end BstLean.Part269.N12582

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12582
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12582 BstLean.Part154.csC) (piBar (rhoBar 12582 BstLean.Part154.csC)) ≤ 1.62909E-7 := by
  have hr0 : 0 ≤ rhoBar 12582 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12582 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12582 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12582 BstLean.Part154.csC) (piBar (rhoBar 12582 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12582 BstLean.Part154.csC) (piBar (rhoBar 12582 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12582 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194224688 : ℝ) ^ 2 + 0.000123586441 ^ 2 + 3 * 0.000071742854 ^ 2 +
        2 * 0.797885 * 0.000194224688 * 0.000123586441 + 2 * 0.000194224688 * 0.000071742854 +
        4 * 0.797885 * 0.000123586441 * 0.000071742854 := by gcongr
    _ ≤ (1.62909E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12582 BstLean.Part154.csC Θ ≤ 0.002654823293 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12582 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12582 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12582 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12582 BstLean.Part154.csC) (piBar (rhoBar 12582 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12582 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035978227492 * 1.62909E-7 / (0.000254284611 : ℝ) := by gcongr
    _ ≤ 0.002654823293 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12582 BstLean.Part154.csC Θ ≤ 0.002946141610 + 0.000670828622 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12582 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12582 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12582 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035978227492 : ℝ) * ((2 * Θ * 0.000254285005 +
        (6863 / 10000) * 0.000254285005 * 12582 * 0.001017204681) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002946141610 + 0.000670828622 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12582 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12582 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12582 0.011 Θ ∧ gammaRatio 12582 0.011 Θ ≤ 0.000087416609 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12582 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035978227492 : ℝ) * 0.525 / ((1 - 0.011) * 12582) := by gcongr
      _ ≤ (0.000087416609 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12582 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12582 0.011 Θ) :=
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
    badAllowance 12582 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12582 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12582 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12582 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12582 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12582 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12582 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12582 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12582 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12582 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12582 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035978227492 : ℝ) * 12582 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12582 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003621111132 + 0.003325651915 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12582

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12582
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12582 BstLean.Part154.csC) (piBar (rhoBar 12582 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12582 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12582 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12582 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12582 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12582 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12582 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12582 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12582 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12582 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12582 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12582 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12582 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12582 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12582 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052732524844 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12582) ≤ 0.010646721488 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12582 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035978227492)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010646721488 + 2 * 0.737676 / 12582) := by gcongr
    _ ≤ (0.052732524844 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12582 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12582

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12582
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498181934 : ℝ) ≤ plow 12582 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12582) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052873678388)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393782229) : eMP 12582 0.011 xi bn ≤ 0.001199744177 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12582 : ℝ) * (1 - 0.011))) ≤ 0.000593197669 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001393782229 / (12582 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593197669 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593197669 : ℝ) + 3.141593 * 0.052873678388 / (12582 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001199744177 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052873678388)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393782229) : PiBarMP 12582 12 0.011 xi bn ≤ 0.162012925992 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12582 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037333392948 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.550876285217 : ℝ) ≤ √((12582 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.169514575039 : ℝ) ≤ √(12582 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12582) ≤ 0.124208509911 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037333392948 + 0.052873678388 * 1.772454 / (2 * (111.550876285217 : ℝ))) * (1 + 0.001199744177) +
        8 / (12582 * 112.169514575039) + 0.124208509911 := by gcongr
    _ ≤ (0.162012925992 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052873678388)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393782229) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282675296829) :
    parallelOracle 12582 0.011 xi bn cd ≤ 0.163012613903 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12582 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12582 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498181934 : ℝ) ≤ plow 12582 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.169514575039 : ℝ) ≤ √(12582 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282675296829 : ℝ) / (2 * 0.560498181934 * 112.169514575039)) * 0.162012925992 +
        0.282675296829 ^ 2 / (2 * 0.560498181934 * 112.169514575039) := by gcongr
    _ ≤ (0.163012613903 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052873678388) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393782229)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282675296829) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12582 12582 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498181934 : ℝ) ≤ plow 12582 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.169514575039 : ℝ) ≤ √(12582 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12582 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12582 Θ 1.22 ≤ 0.011822289729 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.169514575039 := by gcongr <;> linarith
      _ ≤ (0.011822289729 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12582 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12582 12582 0.011 ≤ 0.008521807973 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12582 12582 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12582 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12582 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12582 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12582 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163012613903 + 0.011822289729 + (0.008521807973 : ℝ) *
        (1 + 2 * (0.282675296829 + 0.011822289729) / (0.560498181934 * 112.169514575039))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12582]

end BstLean.Part269.N12582

/-! The original eight local profiles supply actual 12582 moment certificates. -/
namespace BstLean.Part269.N12582
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12582 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12582 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12582 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052873678388 ∧
    0 ≤ bN 12582 BstLean.Part154.csC (groupTheta g) ∧ bN 12582 BstLean.Part154.csC (groupTheta g) ≤ 0.001393782229 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12582 12582 0.011
      (momentAllowance 12582 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12582 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12582 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12582 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12582 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12582 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229942771985 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12582 0.011
      (momentAllowance 12582 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12582 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12582
/-! The actual computed-centre upper energy formula at 12582. -/
namespace BstLean.Part269.N12582
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12582

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12582
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12582)
open BstLean.Part268 (cell12582)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085842237852
  | 2 => 0.086791635581
  | 3 => 0.087740171856
  | 4 => 0.088689492700
  | 5 => 0.089641581166
  | 6 => 0.090598806361
  | 7 => 0.091563976886
  | 8 => 0.092540398715
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12582 12582 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12582 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12582

/-! Actual upper energy certificates on all 43 source endpoints at 12582. -/
namespace BstLean.Part269.N12582
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12582)
open BstLean.Part268 (cell12582)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12582 (gMinus 12582) (1 - (cell12582 i).lower) ≤ 1 ∧
    energyUpper 12582 (gMinus 12582) (BstLean.Part211.gPlus 12582)
      (finiteEnergy 12582 12582 0.011) (1 - (cell12582 i).lower) ≤
      (cell12582 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨10,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨11,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨12,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨13,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨14,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨15,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨16,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨17,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨18,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨19,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨20,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨21,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨22,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨23,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨24,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨25,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨26,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨27,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨28,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨29,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨30,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨31,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨32,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨33,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨34,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨35,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨36,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨37,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨38,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨39,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨40,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨41,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨42,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨43,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨44,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨45,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨46,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨47,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨48,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨49,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨50,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨51,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12582) (by norm_num)
        (q := 1 - (cell12582 ⟨52,by decide⟩).lower)
        (by norm_num [cell12582]) (by norm_num [cell12582])
      exact ⟨E.1,E.2.trans (by norm_num [cell12582])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12582

/-! Source-cell containment and simple scalar guards at 12582. -/
namespace BstLean.Part269.N12582
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12582)
open BstLean.Part268 (cell12582)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12582 ⟨10,by decide⟩).lower ∧ (cell12582 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12582 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12582 ⟨11,by decide⟩).lower ∧ (cell12582 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12582 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12582 ⟨12,by decide⟩).lower ∧ (cell12582 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12582 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12582 ⟨13,by decide⟩).lower ∧ (cell12582 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12582 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12582 ⟨14,by decide⟩).lower ∧ (cell12582 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12582 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12582 ⟨15,by decide⟩).lower ∧ (cell12582 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12582 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12582 ⟨16,by decide⟩).lower ∧ (cell12582 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12582 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12582 ⟨17,by decide⟩).lower ∧ (cell12582 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12582 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12582 ⟨18,by decide⟩).lower ∧ (cell12582 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12582 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12582 ⟨19,by decide⟩).lower ∧ (cell12582 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12582 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12582 ⟨20,by decide⟩).lower ∧ (cell12582 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12582 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12582 ⟨21,by decide⟩).lower ∧ (cell12582 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12582 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12582 ⟨22,by decide⟩).lower ∧ (cell12582 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12582 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12582 ⟨23,by decide⟩).lower ∧ (cell12582 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12582 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12582 ⟨24,by decide⟩).lower ∧ (cell12582 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12582 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12582 ⟨25,by decide⟩).lower ∧ (cell12582 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12582 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12582 ⟨26,by decide⟩).lower ∧ (cell12582 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12582 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12582 ⟨27,by decide⟩).lower ∧ (cell12582 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12582 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12582 ⟨28,by decide⟩).lower ∧ (cell12582 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12582 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12582 ⟨29,by decide⟩).lower ∧ (cell12582 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12582 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12582 ⟨30,by decide⟩).lower ∧ (cell12582 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12582 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12582 ⟨31,by decide⟩).lower ∧ (cell12582 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12582 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12582 ⟨32,by decide⟩).lower ∧ (cell12582 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12582 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12582 ⟨33,by decide⟩).lower ∧ (cell12582 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12582 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12582 ⟨34,by decide⟩).lower ∧ (cell12582 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12582 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12582 ⟨35,by decide⟩).lower ∧ (cell12582 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12582 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12582 ⟨36,by decide⟩).lower ∧ (cell12582 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12582 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12582 ⟨37,by decide⟩).lower ∧ (cell12582 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12582 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12582 ⟨38,by decide⟩).lower ∧ (cell12582 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12582 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12582 ⟨39,by decide⟩).lower ∧ (cell12582 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12582 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12582 ⟨40,by decide⟩).lower ∧ (cell12582 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12582 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12582 ⟨41,by decide⟩).lower ∧ (cell12582 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12582 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12582 ⟨42,by decide⟩).lower ∧ (cell12582 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12582 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12582 ⟨43,by decide⟩).lower ∧ (cell12582 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12582 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12582 ⟨44,by decide⟩).lower ∧ (cell12582 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12582 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12582 ⟨45,by decide⟩).lower ∧ (cell12582 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12582 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12582 ⟨46,by decide⟩).lower ∧ (cell12582 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12582 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12582 ⟨47,by decide⟩).lower ∧ (cell12582 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12582 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12582 ⟨48,by decide⟩).lower ∧ (cell12582 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12582 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12582 ⟨49,by decide⟩).lower ∧ (cell12582 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12582 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12582 ⟨50,by decide⟩).lower ∧ (cell12582 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12582 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12582 ⟨51,by decide⟩).lower ∧ (cell12582 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12582 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12582 ⟨52,by decide⟩).lower ∧ (cell12582 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12582 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12582 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12582 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12582,cell12582,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12582 i).lower ∧
    (cell12582 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12582 i).upper ≤ (0.532 : ℝ) ∧
    (cell12582 i).centre ≤ (0.1 : ℝ) ∧ (cell12582 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12582 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12582 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12582

/-! The local source numeric instances at 12582 have no network premises. -/
namespace BstLean.Part269.N12582
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12582)
open BstLean.Part268 (cell12582)

noncomputable def sourceNumerics12582 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12582 (cell12582 i)
      scalarRow12582.M scalarRow12582.H scalarRow12582.xi := by
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
    energy_allowance := scalarRow12582.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12582]
    centre_nonneg := (scalarRow12582.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12582])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12582
/-! Actual 12583 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12583
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12583 ≤ (1.035976785195 : ℝ) := by
  have hr : (112.173972025599 : ℝ) ≤ √(12583 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.173972025599 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12583 12583 (11 / 1000) ≤
    (0.008521469339 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12583) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.173972025599 : ℝ) ≤ √(12583 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12583)
  have hdiv : K / √(12583 : ℝ) ≤ K / 112.173972025599 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.173972025599 ≤ (0.008521469339 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12583.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12583 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12583 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12583 := gPlus_lower 12583
end BstLean.Part269.N12583

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12583
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035976785194 : ℝ) ≤ wn 12583 := by
  have hn : √(12583 : ℝ) ≤ 112.173972025600 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12583 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.173972025600 ≤ 2 / √(12583 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254264049 : ℝ) ≤ rhoBar 12583 BstLean.Part154.csC ∧
    rhoBar 12583 BstLean.Part154.csC ≤ 0.000254264442 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035976785194 : ℝ) / (1.295212 * 12583) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035976785195 : ℝ) / (1.29521 * 12583) := by gcongr
      _ ≤ (0.000254264442 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12583 BstLean.Part154.csC) ≤ 0.001017122419 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12583 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12583 BstLean.Part154.csC) (piBar (rhoBar 12583 BstLean.Part154.csC)) ≤ 0.000194208982 ∧
    cc1 (rhoBar 12583 BstLean.Part154.csC) (piBar (rhoBar 12583 BstLean.Part154.csC)) ≤ 0.000123576447 ∧
    cc2 (rhoBar 12583 BstLean.Part154.csC) ≤ 0.000071737053 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12583 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12583 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12583 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12583 BstLean.Part154.csC * nuR (rhoBar 12583 BstLean.Part154.csC)) ≤ 0.000508545047 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254264442 : ℝ) * 0.001017122419 := by gcongr
      _ ≤ (0.000508545047 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12583 BstLean.Part154.csC) * nuR (rhoBar 12583 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001017122419 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12583 BstLean.Part154.csC) * rhoBar 12583 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254264442 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254264442 / 2 + 0.399 * 0.001017122419 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194208982 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508545047 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123576447 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254264442 / 1.414213562 := by gcongr
      _ ≤ (0.000071737053 : ℝ) := by norm_num

end BstLean.Part269.N12583

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12583
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12583 BstLean.Part154.csC) (piBar (rhoBar 12583 BstLean.Part154.csC)) ≤ 1.62882E-7 := by
  have hr0 : 0 ≤ rhoBar 12583 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12583 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12583 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12583 BstLean.Part154.csC) (piBar (rhoBar 12583 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12583 BstLean.Part154.csC) (piBar (rhoBar 12583 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12583 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194208982 : ℝ) ^ 2 + 0.000123576447 ^ 2 + 3 * 0.000071737053 ^ 2 +
        2 * 0.797885 * 0.000194208982 * 0.000123576447 + 2 * 0.000194208982 * 0.000071737053 +
        4 * 0.797885 * 0.000123576447 * 0.000071737053 := by gcongr
    _ ≤ (1.62882E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12583 BstLean.Part154.csC Θ ≤ 0.002654594252 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12583 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12583 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12583 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12583 BstLean.Part154.csC) (piBar (rhoBar 12583 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12583 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035976785195 * 1.62882E-7 / (0.000254264049 : ℝ) := by gcongr
    _ ≤ 0.002654594252 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12583 BstLean.Part154.csC Θ ≤ 0.002945895147 + 0.000670773441 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12583 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12583 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12583 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035976785195 : ℝ) * ((2 * Θ * 0.000254264442 +
        (6863 / 10000) * 0.000254264442 * 12583 * 0.001017122419) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002945895147 + 0.000670773441 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12583 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12583 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12583 0.011 Θ ∧ gammaRatio 12583 0.011 Θ ≤ 0.000087409540 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12583 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035976785195 : ℝ) * 0.525 / ((1 - 0.011) * 12583) := by gcongr
      _ ≤ (0.000087409540 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12583 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12583 0.011 Θ) :=
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
    badAllowance 12583 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12583 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12583 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12583 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12583 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12583 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12583 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12583 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12583 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12583 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12583 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035976785195 : ℝ) * 12583 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12583 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003620864669 + 0.003325367693 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12583

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12583
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12583 BstLean.Part154.csC) (piBar (rhoBar 12583 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12583 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12583 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12583 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12583 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12583 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12583 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12583 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12583 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12583 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12583 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12583 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12583 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12583 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12583 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052730406590 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12583) ≤ 0.010646298420 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12583 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035976785195)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010646298420 + 2 * 0.737676 / 12583) := by gcongr
    _ ≤ (0.052730406590 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12583 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12583

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12583
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498228006 : ℝ) ≤ plow 12583 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12583) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052873282708)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393661983) : eMP 12583 0.011 xi bn ≤ 0.001199644696 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12583 : ℝ) * (1 - 0.011))) ≤ 0.000593148509 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001393661983 / (12583 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593148509 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593148509 : ℝ) + 3.141593 * 0.052873282708 / (12583 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001199644696 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052873282708)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393661983) : PiBarMP 12583 12 0.011 xi bn ≤ 0.162006353634 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12583 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037331782479 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.555309152007 : ℝ) ≤ √((12583 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.173972025599 : ℝ) ≤ √(12583 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12583) ≤ 0.124203574245 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037331782479 + 0.052873282708 * 1.772454 / (2 * (111.555309152007 : ℝ))) * (1 + 0.001199644696) +
        8 / (12583 * 112.173972025599) + 0.124203574245 := by gcongr
    _ ≤ (0.162006353634 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052873282708)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393661983) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282672318186) :
    parallelOracle 12583 0.011 xi bn cd ≤ 0.163005969735 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12583 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12583 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498228006 : ℝ) ≤ plow 12583 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.173972025599 : ℝ) ≤ √(12583 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282672318186 : ℝ) / (2 * 0.560498228006 * 112.173972025599)) * 0.162006353634 +
        0.282672318186 ^ 2 / (2 * 0.560498228006 * 112.173972025599) := by gcongr
    _ ≤ (0.163005969735 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052873282708) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393661983)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282672318186) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12583 12583 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498228006 : ℝ) ≤ plow 12583 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.173972025599 : ℝ) ≤ √(12583 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12583 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12583 Θ 1.22 ≤ 0.011821819947 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.173972025599 := by gcongr <;> linarith
      _ ≤ (0.011821819947 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12583 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12583 12583 0.011 ≤ 0.008521469339 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12583 12583 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12583 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12583 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12583 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12583 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163005969735 + 0.011821819947 + (0.008521469339 : ℝ) *
        (1 + 2 * (0.282672318186 + 0.011821819947) / (0.560498228006 * 112.173972025599))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12583]

end BstLean.Part269.N12583

/-! The original eight local profiles supply actual 12583 moment certificates. -/
namespace BstLean.Part269.N12583
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12583 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12583 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12583 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052873282708 ∧
    0 ≤ bN 12583 BstLean.Part154.csC (groupTheta g) ∧ bN 12583 BstLean.Part154.csC (groupTheta g) ≤ 0.001393661983 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12583 12583 0.011
      (momentAllowance 12583 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12583 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12583 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12583 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12583 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12583 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229941911596 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12583 0.011
      (momentAllowance 12583 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12583 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12583
/-! The actual computed-centre upper energy formula at 12583. -/
namespace BstLean.Part269.N12583
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12583

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12583
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12583)
open BstLean.Part268 (cell12583)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085839186216
  | 2 => 0.086788524719
  | 3 => 0.087736992626
  | 4 => 0.088686233891
  | 5 => 0.089638229142
  | 6 => 0.090595344657
  | 7 => 0.091560385762
  | 8 => 0.092536654660
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12583 12583 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12583 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12583

/-! Actual upper energy certificates on all 43 source endpoints at 12583. -/
namespace BstLean.Part269.N12583
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12583)
open BstLean.Part268 (cell12583)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12583 (gMinus 12583) (1 - (cell12583 i).lower) ≤ 1 ∧
    energyUpper 12583 (gMinus 12583) (BstLean.Part211.gPlus 12583)
      (finiteEnergy 12583 12583 0.011) (1 - (cell12583 i).lower) ≤
      (cell12583 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨10,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨11,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨12,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨13,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨14,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨15,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨16,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨17,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨18,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨19,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨20,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨21,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨22,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨23,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨24,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨25,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨26,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨27,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨28,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨29,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨30,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨31,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨32,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨33,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨34,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨35,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨36,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨37,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨38,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨39,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨40,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨41,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨42,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨43,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨44,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨45,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨46,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨47,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨48,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨49,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨50,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨51,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12583) (by norm_num)
        (q := 1 - (cell12583 ⟨52,by decide⟩).lower)
        (by norm_num [cell12583]) (by norm_num [cell12583])
      exact ⟨E.1,E.2.trans (by norm_num [cell12583])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12583

/-! Source-cell containment and simple scalar guards at 12583. -/
namespace BstLean.Part269.N12583
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12583)
open BstLean.Part268 (cell12583)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12583 ⟨10,by decide⟩).lower ∧ (cell12583 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12583 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12583 ⟨11,by decide⟩).lower ∧ (cell12583 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12583 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12583 ⟨12,by decide⟩).lower ∧ (cell12583 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12583 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12583 ⟨13,by decide⟩).lower ∧ (cell12583 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12583 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12583 ⟨14,by decide⟩).lower ∧ (cell12583 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12583 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12583 ⟨15,by decide⟩).lower ∧ (cell12583 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12583 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12583 ⟨16,by decide⟩).lower ∧ (cell12583 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12583 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12583 ⟨17,by decide⟩).lower ∧ (cell12583 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12583 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12583 ⟨18,by decide⟩).lower ∧ (cell12583 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12583 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12583 ⟨19,by decide⟩).lower ∧ (cell12583 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12583 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12583 ⟨20,by decide⟩).lower ∧ (cell12583 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12583 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12583 ⟨21,by decide⟩).lower ∧ (cell12583 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12583 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12583 ⟨22,by decide⟩).lower ∧ (cell12583 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12583 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12583 ⟨23,by decide⟩).lower ∧ (cell12583 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12583 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12583 ⟨24,by decide⟩).lower ∧ (cell12583 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12583 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12583 ⟨25,by decide⟩).lower ∧ (cell12583 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12583 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12583 ⟨26,by decide⟩).lower ∧ (cell12583 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12583 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12583 ⟨27,by decide⟩).lower ∧ (cell12583 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12583 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12583 ⟨28,by decide⟩).lower ∧ (cell12583 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12583 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12583 ⟨29,by decide⟩).lower ∧ (cell12583 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12583 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12583 ⟨30,by decide⟩).lower ∧ (cell12583 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12583 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12583 ⟨31,by decide⟩).lower ∧ (cell12583 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12583 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12583 ⟨32,by decide⟩).lower ∧ (cell12583 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12583 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12583 ⟨33,by decide⟩).lower ∧ (cell12583 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12583 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12583 ⟨34,by decide⟩).lower ∧ (cell12583 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12583 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12583 ⟨35,by decide⟩).lower ∧ (cell12583 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12583 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12583 ⟨36,by decide⟩).lower ∧ (cell12583 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12583 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12583 ⟨37,by decide⟩).lower ∧ (cell12583 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12583 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12583 ⟨38,by decide⟩).lower ∧ (cell12583 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12583 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12583 ⟨39,by decide⟩).lower ∧ (cell12583 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12583 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12583 ⟨40,by decide⟩).lower ∧ (cell12583 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12583 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12583 ⟨41,by decide⟩).lower ∧ (cell12583 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12583 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12583 ⟨42,by decide⟩).lower ∧ (cell12583 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12583 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12583 ⟨43,by decide⟩).lower ∧ (cell12583 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12583 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12583 ⟨44,by decide⟩).lower ∧ (cell12583 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12583 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12583 ⟨45,by decide⟩).lower ∧ (cell12583 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12583 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12583 ⟨46,by decide⟩).lower ∧ (cell12583 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12583 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12583 ⟨47,by decide⟩).lower ∧ (cell12583 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12583 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12583 ⟨48,by decide⟩).lower ∧ (cell12583 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12583 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12583 ⟨49,by decide⟩).lower ∧ (cell12583 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12583 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12583 ⟨50,by decide⟩).lower ∧ (cell12583 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12583 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12583 ⟨51,by decide⟩).lower ∧ (cell12583 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12583 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12583 ⟨52,by decide⟩).lower ∧ (cell12583 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12583 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12583 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12583 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12583,cell12583,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12583 i).lower ∧
    (cell12583 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12583 i).upper ≤ (0.532 : ℝ) ∧
    (cell12583 i).centre ≤ (0.1 : ℝ) ∧ (cell12583 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12583 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12583 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12583

/-! The local source numeric instances at 12583 have no network premises. -/
namespace BstLean.Part269.N12583
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12583)
open BstLean.Part268 (cell12583)

noncomputable def sourceNumerics12583 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12583 (cell12583 i)
      scalarRow12583.M scalarRow12583.H scalarRow12583.xi := by
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
    energy_allowance := scalarRow12583.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12583]
    centre_nonneg := (scalarRow12583.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12583])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12583
/-! Actual 12584 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12584
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12584 ≤ (1.035975343071 : ℝ) := by
  have hr : (112.178429299041 : ℝ) ≤ √(12584 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.178429299041 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12584 12584 (11 / 1000) ≤
    (0.008521130747 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12584) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.178429299041 : ℝ) ≤ √(12584 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12584)
  have hdiv : K / √(12584 : ℝ) ≤ K / 112.178429299041 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.178429299041 ≤ (0.008521130747 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12584.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12584 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12584 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12584 := gPlus_lower 12584
end BstLean.Part269.N12584

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12584
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035975343070 : ℝ) ≤ wn 12584 := by
  have hn : √(12584 : ℝ) ≤ 112.178429299042 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12584 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.178429299042 ≤ 2 / √(12584 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254243489 : ℝ) ≤ rhoBar 12584 BstLean.Part154.csC ∧
    rhoBar 12584 BstLean.Part154.csC ≤ 0.000254243883 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035975343070 : ℝ) / (1.295212 * 12584) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035975343071 : ℝ) / (1.29521 * 12584) := by gcongr
      _ ≤ (0.000254243883 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12584 BstLean.Part154.csC) ≤ 0.001017040172 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12584 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12584 BstLean.Part154.csC) (piBar (rhoBar 12584 BstLean.Part154.csC)) ≤ 0.000194193278 ∧
    cc1 (rhoBar 12584 BstLean.Part154.csC) (piBar (rhoBar 12584 BstLean.Part154.csC)) ≤ 0.000123566455 ∧
    cc2 (rhoBar 12584 BstLean.Part154.csC) ≤ 0.000071731252 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12584 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12584 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12584 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12584 BstLean.Part154.csC * nuR (rhoBar 12584 BstLean.Part154.csC)) ≤ 0.000508503926 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254243883 : ℝ) * 0.001017040172 := by gcongr
      _ ≤ (0.000508503926 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12584 BstLean.Part154.csC) * nuR (rhoBar 12584 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001017040172 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12584 BstLean.Part154.csC) * rhoBar 12584 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254243883 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254243883 / 2 + 0.399 * 0.001017040172 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194193278 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508503926 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123566455 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254243883 / 1.414213562 := by gcongr
      _ ≤ (0.000071731252 : ℝ) := by norm_num

end BstLean.Part269.N12584

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12584
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12584 BstLean.Part154.csC) (piBar (rhoBar 12584 BstLean.Part154.csC)) ≤ 1.62856E-7 := by
  have hr0 : 0 ≤ rhoBar 12584 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12584 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12584 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12584 BstLean.Part154.csC) (piBar (rhoBar 12584 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12584 BstLean.Part154.csC) (piBar (rhoBar 12584 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12584 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194193278 : ℝ) ^ 2 + 0.000123566455 ^ 2 + 3 * 0.000071731252 ^ 2 +
        2 * 0.797885 * 0.000194193278 * 0.000123566455 + 2 * 0.000194193278 * 0.000071731252 +
        4 * 0.797885 * 0.000123566455 * 0.000071731252 := by gcongr
    _ ≤ (1.62856E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12584 BstLean.Part154.csC Θ ≤ 0.002654381454 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12584 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12584 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12584 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12584 BstLean.Part154.csC) (piBar (rhoBar 12584 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12584 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035975343071 * 1.62856E-7 / (0.000254243489 : ℝ) := by gcongr
    _ ≤ 0.002654381454 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12584 BstLean.Part154.csC Θ ≤ 0.002945648737 + 0.000670718271 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12584 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12584 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12584 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035975343071 : ℝ) * ((2 * Θ * 0.000254243883 +
        (6863 / 10000) * 0.000254243883 * 12584 * 0.001017040172) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002945648737 + 0.000670718271 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12584 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12584 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12584 0.011 Θ ∧ gammaRatio 12584 0.011 Θ ≤ 0.000087402473 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12584 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035975343071 : ℝ) * 0.525 / ((1 - 0.011) * 12584) := by gcongr
      _ ≤ (0.000087402473 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12584 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12584 0.011 Θ) :=
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
    badAllowance 12584 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12584 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12584 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12584 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12584 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12584 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12584 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12584 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12584 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12584 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12584 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035975343071 : ℝ) * 12584 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12584 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003620618259 + 0.003325099725 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12584

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12584
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12584 BstLean.Part154.csC) (piBar (rhoBar 12584 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12584 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12584 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12584 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12584 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12584 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12584 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12584 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12584 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12584 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12584 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12584 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12584 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12584 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12584 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052728288588 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12584) ≤ 0.010645875402 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12584 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035975343071)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010645875402 + 2 * 0.737676 / 12584) := by gcongr
    _ ≤ (0.052728288588 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12584 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12584

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12584
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498274070 : ℝ) ≤ plow 12584 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12584) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052872895615)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393550264) : eMP 12584 0.011 xi bn ≤ 0.001199548856 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12584 : ℝ) * (1 - 0.011))) ≤ 0.000593101168 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001393550264 / (12584 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593101168 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593101168 : ℝ) + 3.141593 * 0.052872895615 / (12584 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001199548856 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052872895615)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393550264) : PiBarMP 12584 12 0.011 xi bn ≤ 0.161999896350 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12584 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037330286150 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.559741842655 : ℝ) ≤ √((12584 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.178429299041 : ℝ) ≤ √(12584 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12584) ≤ 0.124198639167 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037330286150 + 0.052872895615 * 1.772454 / (2 * (111.559741842655 : ℝ))) * (1 + 0.001199548856) +
        8 / (12584 * 112.178429299041) + 0.124198639167 := by gcongr
    _ ≤ (0.161999896350 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052872895615)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393550264) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282669358463) :
    parallelOracle 12584 0.011 xi bn cd ≤ 0.162999441016 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12584 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12584 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498274070 : ℝ) ≤ plow 12584 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.178429299041 : ℝ) ≤ √(12584 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282669358463 : ℝ) / (2 * 0.560498274070 * 112.178429299041)) * 0.161999896350 +
        0.282669358463 ^ 2 / (2 * 0.560498274070 * 112.178429299041) := by gcongr
    _ ≤ (0.162999441016 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052872895615) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393550264)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282669358463) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12584 12584 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498274070 : ℝ) ≤ plow 12584 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.178429299041 : ℝ) ≤ √(12584 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12584 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12584 Θ 1.22 ≤ 0.011821350222 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.178429299041 := by gcongr <;> linarith
      _ ≤ (0.011821350222 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12584 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12584 12584 0.011 ≤ 0.008521130747 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12584 12584 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12584 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12584 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12584 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12584 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162999441016 + 0.011821350222 + (0.008521130747 : ℝ) *
        (1 + 2 * (0.282669358463 + 0.011821350222) / (0.560498274070 * 112.178429299041))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12584]

end BstLean.Part269.N12584

/-! The original eight local profiles supply actual 12584 moment certificates. -/
namespace BstLean.Part269.N12584
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12584 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12584 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12584 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052872895615 ∧
    0 ≤ bN 12584 BstLean.Part154.csC (groupTheta g) ∧ bN 12584 BstLean.Part154.csC (groupTheta g) ≤ 0.001393550264 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12584 12584 0.011
      (momentAllowance 12584 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12584 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12584 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12584 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12584 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12584 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229941069875 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12584 0.011
      (momentAllowance 12584 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12584 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12584
/-! The actual computed-centre upper energy formula at 12584. -/
namespace BstLean.Part269.N12584
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12584

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12584
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12584)
open BstLean.Part268 (cell12584)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085836135803
  | 2 => 0.086785415132
  | 3 => 0.087733814733
  | 4 => 0.088682976498
  | 5 => 0.089634878631
  | 6 => 0.090591884582
  | 7 => 0.091556796408
  | 8 => 0.092532912544
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12584 12584 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12584 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12584

/-! Actual upper energy certificates on all 43 source endpoints at 12584. -/
namespace BstLean.Part269.N12584
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12584)
open BstLean.Part268 (cell12584)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12584 (gMinus 12584) (1 - (cell12584 i).lower) ≤ 1 ∧
    energyUpper 12584 (gMinus 12584) (BstLean.Part211.gPlus 12584)
      (finiteEnergy 12584 12584 0.011) (1 - (cell12584 i).lower) ≤
      (cell12584 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨10,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨11,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨12,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨13,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨14,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨15,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨16,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨17,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨18,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨19,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨20,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨21,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨22,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨23,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨24,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨25,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨26,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨27,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨28,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨29,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨30,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨31,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨32,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨33,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨34,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨35,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨36,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨37,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨38,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨39,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨40,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨41,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨42,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨43,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨44,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨45,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨46,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨47,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨48,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨49,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨50,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨51,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12584) (by norm_num)
        (q := 1 - (cell12584 ⟨52,by decide⟩).lower)
        (by norm_num [cell12584]) (by norm_num [cell12584])
      exact ⟨E.1,E.2.trans (by norm_num [cell12584])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12584

/-! Source-cell containment and simple scalar guards at 12584. -/
namespace BstLean.Part269.N12584
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12584)
open BstLean.Part268 (cell12584)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12584 ⟨10,by decide⟩).lower ∧ (cell12584 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12584 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12584 ⟨11,by decide⟩).lower ∧ (cell12584 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12584 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12584 ⟨12,by decide⟩).lower ∧ (cell12584 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12584 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12584 ⟨13,by decide⟩).lower ∧ (cell12584 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12584 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12584 ⟨14,by decide⟩).lower ∧ (cell12584 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12584 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12584 ⟨15,by decide⟩).lower ∧ (cell12584 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12584 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12584 ⟨16,by decide⟩).lower ∧ (cell12584 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12584 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12584 ⟨17,by decide⟩).lower ∧ (cell12584 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12584 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12584 ⟨18,by decide⟩).lower ∧ (cell12584 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12584 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12584 ⟨19,by decide⟩).lower ∧ (cell12584 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12584 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12584 ⟨20,by decide⟩).lower ∧ (cell12584 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12584 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12584 ⟨21,by decide⟩).lower ∧ (cell12584 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12584 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12584 ⟨22,by decide⟩).lower ∧ (cell12584 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12584 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12584 ⟨23,by decide⟩).lower ∧ (cell12584 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12584 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12584 ⟨24,by decide⟩).lower ∧ (cell12584 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12584 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12584 ⟨25,by decide⟩).lower ∧ (cell12584 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12584 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12584 ⟨26,by decide⟩).lower ∧ (cell12584 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12584 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12584 ⟨27,by decide⟩).lower ∧ (cell12584 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12584 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12584 ⟨28,by decide⟩).lower ∧ (cell12584 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12584 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12584 ⟨29,by decide⟩).lower ∧ (cell12584 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12584 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12584 ⟨30,by decide⟩).lower ∧ (cell12584 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12584 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12584 ⟨31,by decide⟩).lower ∧ (cell12584 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12584 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12584 ⟨32,by decide⟩).lower ∧ (cell12584 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12584 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12584 ⟨33,by decide⟩).lower ∧ (cell12584 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12584 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12584 ⟨34,by decide⟩).lower ∧ (cell12584 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12584 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12584 ⟨35,by decide⟩).lower ∧ (cell12584 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12584 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12584 ⟨36,by decide⟩).lower ∧ (cell12584 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12584 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12584 ⟨37,by decide⟩).lower ∧ (cell12584 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12584 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12584 ⟨38,by decide⟩).lower ∧ (cell12584 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12584 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12584 ⟨39,by decide⟩).lower ∧ (cell12584 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12584 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12584 ⟨40,by decide⟩).lower ∧ (cell12584 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12584 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12584 ⟨41,by decide⟩).lower ∧ (cell12584 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12584 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12584 ⟨42,by decide⟩).lower ∧ (cell12584 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12584 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12584 ⟨43,by decide⟩).lower ∧ (cell12584 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12584 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12584 ⟨44,by decide⟩).lower ∧ (cell12584 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12584 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12584 ⟨45,by decide⟩).lower ∧ (cell12584 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12584 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12584 ⟨46,by decide⟩).lower ∧ (cell12584 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12584 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12584 ⟨47,by decide⟩).lower ∧ (cell12584 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12584 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12584 ⟨48,by decide⟩).lower ∧ (cell12584 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12584 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12584 ⟨49,by decide⟩).lower ∧ (cell12584 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12584 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12584 ⟨50,by decide⟩).lower ∧ (cell12584 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12584 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12584 ⟨51,by decide⟩).lower ∧ (cell12584 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12584 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12584 ⟨52,by decide⟩).lower ∧ (cell12584 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12584 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12584 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12584 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12584,cell12584,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12584 i).lower ∧
    (cell12584 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12584 i).upper ≤ (0.532 : ℝ) ∧
    (cell12584 i).centre ≤ (0.1 : ℝ) ∧ (cell12584 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12584 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12584 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12584

/-! The local source numeric instances at 12584 have no network premises. -/
namespace BstLean.Part269.N12584
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12584)
open BstLean.Part268 (cell12584)

noncomputable def sourceNumerics12584 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12584 (cell12584 i)
      scalarRow12584.M scalarRow12584.H scalarRow12584.xi := by
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
    energy_allowance := scalarRow12584.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12584]
    centre_nonneg := (scalarRow12584.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12584])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12584
/-! Actual 12585 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12585
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12585 ≤ (1.035973901119 : ℝ) := by
  have hr : (112.182886395385 : ℝ) ≤ √(12585 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.182886395385 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12585 12585 (11 / 1000) ≤
    (0.008520792194 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12585) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.182886395385 : ℝ) ≤ √(12585 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12585)
  have hdiv : K / √(12585 : ℝ) ≤ K / 112.182886395385 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.182886395385 ≤ (0.008520792194 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12585.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12585 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12585 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12585 := gPlus_lower 12585
end BstLean.Part269.N12585

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12585
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035973901118 : ℝ) ≤ wn 12585 := by
  have hn : √(12585 : ℝ) ≤ 112.182886395386 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12585 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.182886395386 ≤ 2 / √(12585 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254222933 : ℝ) ≤ rhoBar 12585 BstLean.Part154.csC ∧
    rhoBar 12585 BstLean.Part154.csC ≤ 0.000254223327 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035973901118 : ℝ) / (1.295212 * 12585) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035973901119 : ℝ) / (1.29521 * 12585) := by gcongr
      _ ≤ (0.000254223327 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12585 BstLean.Part154.csC) ≤ 0.001016957938 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12585 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12585 BstLean.Part154.csC) (piBar (rhoBar 12585 BstLean.Part154.csC)) ≤ 0.000194177576 ∧
    cc1 (rhoBar 12585 BstLean.Part154.csC) (piBar (rhoBar 12585 BstLean.Part154.csC)) ≤ 0.000123556464 ∧
    cc2 (rhoBar 12585 BstLean.Part154.csC) ≤ 0.000071725453 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12585 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12585 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12585 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12585 BstLean.Part154.csC * nuR (rhoBar 12585 BstLean.Part154.csC)) ≤ 0.000508462812 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254223327 : ℝ) * 0.001016957938 := by gcongr
      _ ≤ (0.000508462812 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12585 BstLean.Part154.csC) * nuR (rhoBar 12585 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001016957938 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12585 BstLean.Part154.csC) * rhoBar 12585 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254223327 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254223327 / 2 + 0.399 * 0.001016957938 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194177576 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508462812 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123556464 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254223327 / 1.414213562 := by gcongr
      _ ≤ (0.000071725453 : ℝ) := by norm_num

end BstLean.Part269.N12585

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12585
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12585 BstLean.Part154.csC) (piBar (rhoBar 12585 BstLean.Part154.csC)) ≤ 1.62830E-7 := by
  have hr0 : 0 ≤ rhoBar 12585 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12585 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12585 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12585 BstLean.Part154.csC) (piBar (rhoBar 12585 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12585 BstLean.Part154.csC) (piBar (rhoBar 12585 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12585 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194177576 : ℝ) ^ 2 + 0.000123556464 ^ 2 + 3 * 0.000071725453 ^ 2 +
        2 * 0.797885 * 0.000194177576 * 0.000123556464 + 2 * 0.000194177576 * 0.000071725453 +
        4 * 0.797885 * 0.000123556464 * 0.000071725453 := by gcongr
    _ ≤ (1.62830E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12585 BstLean.Part154.csC Θ ≤ 0.002654168581 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12585 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12585 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12585 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12585 BstLean.Part154.csC) (piBar (rhoBar 12585 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12585 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035973901119 * 1.62830E-7 / (0.000254222933 : ℝ) := by gcongr
    _ ≤ 0.002654168581 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12585 BstLean.Part154.csC Θ ≤ 0.002945402364 + 0.000670663108 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12585 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12585 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12585 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035973901119 : ℝ) * ((2 * Θ * 0.000254223327 +
        (6863 / 10000) * 0.000254223327 * 12585 * 0.001016957938) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002945402364 + 0.000670663108 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12585 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12585 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12585 0.011 Θ ∧ gammaRatio 12585 0.011 Θ ≤ 0.000087395406 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12585 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035973901119 : ℝ) * 0.525 / ((1 - 0.011) * 12585) := by gcongr
      _ ≤ (0.000087395406 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12585 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12585 0.011 Θ) :=
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
    badAllowance 12585 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12585 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12585 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12585 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12585 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12585 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12585 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12585 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12585 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12585 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12585 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035973901119 : ℝ) * 12585 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12585 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003620371886 + 0.003324831689 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12585

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12585
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12585 BstLean.Part154.csC) (piBar (rhoBar 12585 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12585 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12585 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12585 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12585 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12585 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12585 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12585 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12585 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12585 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12585 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12585 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12585 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12585 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12585 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052726170842 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12585) ≤ 0.010645452435 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12585 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035973901119)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010645452435 + 2 * 0.737676 / 12585) := by gcongr
    _ ≤ (0.052726170842 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12585 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12585

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12585
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498320127 : ℝ) ≤ plow 12585 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12585) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052872508523)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393438506) : eMP 12585 0.011 xi bn ≤ 0.001199453003 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12585 : ℝ) * (1 - 0.011))) ≤ 0.000593053821 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001393438506 / (12585 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593053821 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593053821 : ℝ) + 3.141593 * 0.052872508523 / (12585 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001199453003 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052872508523)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393438506) : PiBarMP 12585 12 0.011 xi bn ≤ 0.161993439073 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12585 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037328789239 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.564174357183 : ℝ) ≤ √((12585 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.182886395385 : ℝ) ≤ √(12585 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12585) ≤ 0.124193704677 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037328789239 + 0.052872508523 * 1.772454 / (2 * (111.564174357183 : ℝ))) * (1 + 0.001199453003) +
        8 / (12585 * 112.182886395385) + 0.124193704677 := by gcongr
    _ ≤ (0.161993439073 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052872508523)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393438506) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282666398995) :
    parallelOracle 12585 0.011 xi bn cd ≤ 0.162992912314 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12585 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12585 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498320127 : ℝ) ≤ plow 12585 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.182886395385 : ℝ) ≤ √(12585 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282666398995 : ℝ) / (2 * 0.560498320127 * 112.182886395385)) * 0.161993439073 +
        0.282666398995 ^ 2 / (2 * 0.560498320127 * 112.182886395385) := by gcongr
    _ ≤ (0.162992912314 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052872508523) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393438506)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282666398995) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12585 12585 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498320127 : ℝ) ≤ plow 12585 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.182886395385 : ℝ) ≤ √(12585 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12585 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12585 Θ 1.22 ≤ 0.011820880552 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.182886395385 := by gcongr <;> linarith
      _ ≤ (0.011820880552 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12585 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12585 12585 0.011 ≤ 0.008520792194 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12585 12585 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12585 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12585 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12585 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12585 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162992912314 + 0.011820880552 + (0.008520792194 : ℝ) *
        (1 + 2 * (0.282666398995 + 0.011820880552) / (0.560498320127 * 112.182886395385))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12585]

end BstLean.Part269.N12585

/-! The original eight local profiles supply actual 12585 moment certificates. -/
namespace BstLean.Part269.N12585
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12585 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12585 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12585 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052872508523 ∧
    0 ≤ bN 12585 BstLean.Part154.csC (groupTheta g) ∧ bN 12585 BstLean.Part154.csC (groupTheta g) ≤ 0.001393438506 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12585 12585 0.011
      (momentAllowance 12585 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12585 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12585 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12585 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12585 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12585 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229940228153 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12585 0.011
      (momentAllowance 12585 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12585 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12585
/-! The actual computed-centre upper energy formula at 12585. -/
namespace BstLean.Part269.N12585
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12585

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12585
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12585)
open BstLean.Part268 (cell12585)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085833086612
  | 2 => 0.086782306817
  | 3 => 0.087730638178
  | 4 => 0.088679720521
  | 5 => 0.089631529630
  | 6 => 0.090588426135
  | 7 => 0.091553208822
  | 8 => 0.092529172365
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12585 12585 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12585 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12585

/-! Actual upper energy certificates on all 43 source endpoints at 12585. -/
namespace BstLean.Part269.N12585
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12585)
open BstLean.Part268 (cell12585)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12585 (gMinus 12585) (1 - (cell12585 i).lower) ≤ 1 ∧
    energyUpper 12585 (gMinus 12585) (BstLean.Part211.gPlus 12585)
      (finiteEnergy 12585 12585 0.011) (1 - (cell12585 i).lower) ≤
      (cell12585 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨10,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨11,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨12,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨13,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨14,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨15,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨16,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨17,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨18,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨19,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨20,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨21,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨22,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨23,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨24,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨25,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨26,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨27,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨28,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨29,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨30,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨31,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨32,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨33,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨34,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨35,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨36,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨37,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨38,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨39,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨40,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨41,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨42,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨43,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨44,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨45,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨46,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨47,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨48,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨49,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨50,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨51,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12585) (by norm_num)
        (q := 1 - (cell12585 ⟨52,by decide⟩).lower)
        (by norm_num [cell12585]) (by norm_num [cell12585])
      exact ⟨E.1,E.2.trans (by norm_num [cell12585])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12585

/-! Source-cell containment and simple scalar guards at 12585. -/
namespace BstLean.Part269.N12585
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12585)
open BstLean.Part268 (cell12585)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12585 ⟨10,by decide⟩).lower ∧ (cell12585 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12585 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12585 ⟨11,by decide⟩).lower ∧ (cell12585 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12585 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12585 ⟨12,by decide⟩).lower ∧ (cell12585 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12585 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12585 ⟨13,by decide⟩).lower ∧ (cell12585 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12585 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12585 ⟨14,by decide⟩).lower ∧ (cell12585 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12585 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12585 ⟨15,by decide⟩).lower ∧ (cell12585 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12585 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12585 ⟨16,by decide⟩).lower ∧ (cell12585 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12585 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12585 ⟨17,by decide⟩).lower ∧ (cell12585 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12585 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12585 ⟨18,by decide⟩).lower ∧ (cell12585 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12585 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12585 ⟨19,by decide⟩).lower ∧ (cell12585 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12585 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12585 ⟨20,by decide⟩).lower ∧ (cell12585 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12585 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12585 ⟨21,by decide⟩).lower ∧ (cell12585 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12585 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12585 ⟨22,by decide⟩).lower ∧ (cell12585 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12585 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12585 ⟨23,by decide⟩).lower ∧ (cell12585 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12585 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12585 ⟨24,by decide⟩).lower ∧ (cell12585 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12585 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12585 ⟨25,by decide⟩).lower ∧ (cell12585 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12585 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12585 ⟨26,by decide⟩).lower ∧ (cell12585 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12585 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12585 ⟨27,by decide⟩).lower ∧ (cell12585 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12585 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12585 ⟨28,by decide⟩).lower ∧ (cell12585 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12585 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12585 ⟨29,by decide⟩).lower ∧ (cell12585 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12585 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12585 ⟨30,by decide⟩).lower ∧ (cell12585 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12585 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12585 ⟨31,by decide⟩).lower ∧ (cell12585 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12585 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12585 ⟨32,by decide⟩).lower ∧ (cell12585 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12585 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12585 ⟨33,by decide⟩).lower ∧ (cell12585 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12585 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12585 ⟨34,by decide⟩).lower ∧ (cell12585 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12585 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12585 ⟨35,by decide⟩).lower ∧ (cell12585 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12585 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12585 ⟨36,by decide⟩).lower ∧ (cell12585 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12585 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12585 ⟨37,by decide⟩).lower ∧ (cell12585 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12585 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12585 ⟨38,by decide⟩).lower ∧ (cell12585 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12585 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12585 ⟨39,by decide⟩).lower ∧ (cell12585 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12585 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12585 ⟨40,by decide⟩).lower ∧ (cell12585 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12585 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12585 ⟨41,by decide⟩).lower ∧ (cell12585 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12585 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12585 ⟨42,by decide⟩).lower ∧ (cell12585 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12585 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12585 ⟨43,by decide⟩).lower ∧ (cell12585 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12585 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12585 ⟨44,by decide⟩).lower ∧ (cell12585 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12585 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12585 ⟨45,by decide⟩).lower ∧ (cell12585 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12585 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12585 ⟨46,by decide⟩).lower ∧ (cell12585 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12585 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12585 ⟨47,by decide⟩).lower ∧ (cell12585 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12585 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12585 ⟨48,by decide⟩).lower ∧ (cell12585 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12585 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12585 ⟨49,by decide⟩).lower ∧ (cell12585 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12585 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12585 ⟨50,by decide⟩).lower ∧ (cell12585 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12585 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12585 ⟨51,by decide⟩).lower ∧ (cell12585 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12585 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12585 ⟨52,by decide⟩).lower ∧ (cell12585 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12585 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12585 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12585 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12585,cell12585,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12585 i).lower ∧
    (cell12585 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12585 i).upper ≤ (0.532 : ℝ) ∧
    (cell12585 i).centre ≤ (0.1 : ℝ) ∧ (cell12585 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12585 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12585 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12585

/-! The local source numeric instances at 12585 have no network premises. -/
namespace BstLean.Part269.N12585
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12585)
open BstLean.Part268 (cell12585)

noncomputable def sourceNumerics12585 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12585 (cell12585 i)
      scalarRow12585.M scalarRow12585.H scalarRow12585.xi := by
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
    energy_allowance := scalarRow12585.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12585]
    centre_nonneg := (scalarRow12585.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12585])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12585
/-! Actual 12586 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12586
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12586 ≤ (1.035972459341 : ℝ) := by
  have hr : (112.187343314653 : ℝ) ≤ √(12586 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.187343314653 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12586 12586 (11 / 1000) ≤
    (0.008520453682 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12586) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.187343314653 : ℝ) ≤ √(12586 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12586)
  have hdiv : K / √(12586 : ℝ) ≤ K / 112.187343314653 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.187343314653 ≤ (0.008520453682 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12586.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12586 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12586 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12586 := gPlus_lower 12586
end BstLean.Part269.N12586

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12586
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035972459340 : ℝ) ≤ wn 12586 := by
  have hn : √(12586 : ℝ) ≤ 112.187343314654 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12586 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.187343314654 ≤ 2 / √(12586 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254202381 : ℝ) ≤ rhoBar 12586 BstLean.Part154.csC ∧
    rhoBar 12586 BstLean.Part154.csC ≤ 0.000254202774 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035972459340 : ℝ) / (1.295212 * 12586) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035972459341 : ℝ) / (1.29521 * 12586) := by gcongr
      _ ≤ (0.000254202774 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12586 BstLean.Part154.csC) ≤ 0.001016875716 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12586 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12586 BstLean.Part154.csC) (piBar (rhoBar 12586 BstLean.Part154.csC)) ≤ 0.000194161877 ∧
    cc1 (rhoBar 12586 BstLean.Part154.csC) (piBar (rhoBar 12586 BstLean.Part154.csC)) ≤ 0.000123546474 ∧
    cc2 (rhoBar 12586 BstLean.Part154.csC) ≤ 0.000071719654 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12586 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12586 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12586 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12586 BstLean.Part154.csC * nuR (rhoBar 12586 BstLean.Part154.csC)) ≤ 0.000508421703 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254202774 : ℝ) * 0.001016875716 := by gcongr
      _ ≤ (0.000508421703 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12586 BstLean.Part154.csC) * nuR (rhoBar 12586 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001016875716 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12586 BstLean.Part154.csC) * rhoBar 12586 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254202774 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254202774 / 2 + 0.399 * 0.001016875716 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194161877 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508421703 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123546474 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254202774 / 1.414213562 := by gcongr
      _ ≤ (0.000071719654 : ℝ) := by norm_num

end BstLean.Part269.N12586

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12586
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12586 BstLean.Part154.csC) (piBar (rhoBar 12586 BstLean.Part154.csC)) ≤ 1.62803E-7 := by
  have hr0 : 0 ≤ rhoBar 12586 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12586 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12586 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12586 BstLean.Part154.csC) (piBar (rhoBar 12586 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12586 BstLean.Part154.csC) (piBar (rhoBar 12586 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12586 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194161877 : ℝ) ^ 2 + 0.000123546474 ^ 2 + 3 * 0.000071719654 ^ 2 +
        2 * 0.797885 * 0.000194161877 * 0.000123546474 + 2 * 0.000194161877 * 0.000071719654 +
        4 * 0.797885 * 0.000123546474 * 0.000071719654 := by gcongr
    _ ≤ (1.62803E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12586 BstLean.Part154.csC Θ ≤ 0.002653939332 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12586 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12586 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12586 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12586 BstLean.Part154.csC) (piBar (rhoBar 12586 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12586 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035972459341 * 1.62803E-7 / (0.000254202381 : ℝ) := by gcongr
    _ ≤ 0.002653939332 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12586 BstLean.Part154.csC Θ ≤ 0.002945156024 + 0.000670607955 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12586 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12586 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12586 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035972459341 : ℝ) * ((2 * Θ * 0.000254202774 +
        (6863 / 10000) * 0.000254202774 * 12586 * 0.001016875716) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002945156024 + 0.000670607955 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12586 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12586 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12586 0.011 Θ ∧ gammaRatio 12586 0.011 Θ ≤ 0.000087388341 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12586 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035972459341 : ℝ) * 0.525 / ((1 - 0.011) * 12586) := by gcongr
      _ ≤ (0.000087388341 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12586 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12586 0.011 Θ) :=
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
    badAllowance 12586 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12586 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12586 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12586 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12586 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12586 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12586 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12586 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12586 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12586 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12586 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035972459341 : ℝ) * 12586 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12586 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003620125546 + 0.003324547287 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12586

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12586
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12586 BstLean.Part154.csC) (piBar (rhoBar 12586 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12586 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12586 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12586 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12586 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12586 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12586 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12586 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12586 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12586 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12586 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12586 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12586 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12586 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12586 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052724053349 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12586) ≤ 0.010645029518 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12586 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035972459341)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010645029518 + 2 * 0.737676 / 12586) := by gcongr
    _ ≤ (0.052724053349 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12586 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12586

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12586
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498366176 : ℝ) ≤ plow 12586 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12586) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052872112872)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393318150) : eMP 12586 0.011 xi bn ≤ 0.001199353499 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12586 : ℝ) * (1 - 0.011))) ≤ 0.000593004649 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001393318150 / (12586 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000593004649 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000593004649 : ℝ) + 3.141593 * 0.052872112872 / (12586 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001199353499 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052872112872)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393318150) : PiBarMP 12586 12 0.011 xi bn ≤ 0.161986866812 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12586 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037327177097 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.568606695611 : ℝ) ≤ √((12586 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.187343314653 : ℝ) ≤ √(12586 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12586) ≤ 0.124188770775 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037327177097 + 0.052872112872 * 1.772454 / (2 * (111.568606695611 : ℝ))) * (1 + 0.001199353499) +
        8 / (12586 * 112.187343314653) + 0.124188770775 := by gcongr
    _ ≤ (0.161986866812 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052872112872)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393318150) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282663421166) :
    parallelOracle 12586 0.011 xi bn cd ≤ 0.162986268270 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12586 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12586 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498366176 : ℝ) ≤ plow 12586 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.187343314653 : ℝ) ≤ √(12586 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282663421166 : ℝ) / (2 * 0.560498366176 * 112.187343314653)) * 0.161986866812 +
        0.282663421166 ^ 2 / (2 * 0.560498366176 * 112.187343314653) := by gcongr
    _ ≤ (0.162986268270 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052872112872) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393318150)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282663421166) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12586 12586 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498366176 : ℝ) ≤ plow 12586 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.187343314653 : ℝ) ≤ √(12586 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12586 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12586 Θ 1.22 ≤ 0.011820410938 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.187343314653 := by gcongr <;> linarith
      _ ≤ (0.011820410938 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12586 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12586 12586 0.011 ≤ 0.008520453682 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12586 12586 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12586 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12586 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12586 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12586 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162986268270 + 0.011820410938 + (0.008520453682 : ℝ) *
        (1 + 2 * (0.282663421166 + 0.011820410938) / (0.560498366176 * 112.187343314653))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12586]

end BstLean.Part269.N12586

/-! The original eight local profiles supply actual 12586 moment certificates. -/
namespace BstLean.Part269.N12586
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12586 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12586 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12586 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052872112872 ∧
    0 ≤ bN 12586 BstLean.Part154.csC (groupTheta g) ∧ bN 12586 BstLean.Part154.csC (groupTheta g) ≤ 0.001393318150 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12586 12586 0.011
      (momentAllowance 12586 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12586 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12586 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12586 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12586 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12586 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229939367817 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12586 0.011
      (momentAllowance 12586 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12586 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12586
/-! The actual computed-centre upper energy formula at 12586. -/
namespace BstLean.Part269.N12586
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12586

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12586
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12586)
open BstLean.Part268 (cell12586)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085830038640
  | 2 => 0.086779199774
  | 3 => 0.087727462958
  | 4 => 0.088676465958
  | 5 => 0.089628182139
  | 6 => 0.090584969313
  | 7 => 0.091549623002
  | 8 => 0.092525434121
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12586 12586 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12586 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12586

/-! Actual upper energy certificates on all 43 source endpoints at 12586. -/
namespace BstLean.Part269.N12586
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12586)
open BstLean.Part268 (cell12586)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12586 (gMinus 12586) (1 - (cell12586 i).lower) ≤ 1 ∧
    energyUpper 12586 (gMinus 12586) (BstLean.Part211.gPlus 12586)
      (finiteEnergy 12586 12586 0.011) (1 - (cell12586 i).lower) ≤
      (cell12586 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨10,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨11,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨12,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨13,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨14,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨15,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨16,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨17,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨18,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨19,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨20,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨21,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨22,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨23,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨24,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨25,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨26,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨27,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨28,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨29,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨30,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨31,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨32,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨33,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨34,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨35,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨36,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨37,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨38,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨39,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨40,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨41,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨42,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨43,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨44,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨45,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨46,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨47,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨48,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨49,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨50,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨51,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12586) (by norm_num)
        (q := 1 - (cell12586 ⟨52,by decide⟩).lower)
        (by norm_num [cell12586]) (by norm_num [cell12586])
      exact ⟨E.1,E.2.trans (by norm_num [cell12586])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12586

/-! Source-cell containment and simple scalar guards at 12586. -/
namespace BstLean.Part269.N12586
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12586)
open BstLean.Part268 (cell12586)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12586 ⟨10,by decide⟩).lower ∧ (cell12586 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12586 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12586 ⟨11,by decide⟩).lower ∧ (cell12586 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12586 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12586 ⟨12,by decide⟩).lower ∧ (cell12586 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12586 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12586 ⟨13,by decide⟩).lower ∧ (cell12586 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12586 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12586 ⟨14,by decide⟩).lower ∧ (cell12586 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12586 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12586 ⟨15,by decide⟩).lower ∧ (cell12586 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12586 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12586 ⟨16,by decide⟩).lower ∧ (cell12586 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12586 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12586 ⟨17,by decide⟩).lower ∧ (cell12586 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12586 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12586 ⟨18,by decide⟩).lower ∧ (cell12586 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12586 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12586 ⟨19,by decide⟩).lower ∧ (cell12586 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12586 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12586 ⟨20,by decide⟩).lower ∧ (cell12586 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12586 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12586 ⟨21,by decide⟩).lower ∧ (cell12586 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12586 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12586 ⟨22,by decide⟩).lower ∧ (cell12586 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12586 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12586 ⟨23,by decide⟩).lower ∧ (cell12586 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12586 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12586 ⟨24,by decide⟩).lower ∧ (cell12586 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12586 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12586 ⟨25,by decide⟩).lower ∧ (cell12586 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12586 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12586 ⟨26,by decide⟩).lower ∧ (cell12586 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12586 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12586 ⟨27,by decide⟩).lower ∧ (cell12586 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12586 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12586 ⟨28,by decide⟩).lower ∧ (cell12586 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12586 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12586 ⟨29,by decide⟩).lower ∧ (cell12586 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12586 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12586 ⟨30,by decide⟩).lower ∧ (cell12586 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12586 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12586 ⟨31,by decide⟩).lower ∧ (cell12586 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12586 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12586 ⟨32,by decide⟩).lower ∧ (cell12586 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12586 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12586 ⟨33,by decide⟩).lower ∧ (cell12586 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12586 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12586 ⟨34,by decide⟩).lower ∧ (cell12586 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12586 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12586 ⟨35,by decide⟩).lower ∧ (cell12586 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12586 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12586 ⟨36,by decide⟩).lower ∧ (cell12586 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12586 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12586 ⟨37,by decide⟩).lower ∧ (cell12586 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12586 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12586 ⟨38,by decide⟩).lower ∧ (cell12586 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12586 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12586 ⟨39,by decide⟩).lower ∧ (cell12586 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12586 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12586 ⟨40,by decide⟩).lower ∧ (cell12586 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12586 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12586 ⟨41,by decide⟩).lower ∧ (cell12586 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12586 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12586 ⟨42,by decide⟩).lower ∧ (cell12586 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12586 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12586 ⟨43,by decide⟩).lower ∧ (cell12586 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12586 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12586 ⟨44,by decide⟩).lower ∧ (cell12586 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12586 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12586 ⟨45,by decide⟩).lower ∧ (cell12586 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12586 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12586 ⟨46,by decide⟩).lower ∧ (cell12586 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12586 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12586 ⟨47,by decide⟩).lower ∧ (cell12586 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12586 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12586 ⟨48,by decide⟩).lower ∧ (cell12586 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12586 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12586 ⟨49,by decide⟩).lower ∧ (cell12586 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12586 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12586 ⟨50,by decide⟩).lower ∧ (cell12586 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12586 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12586 ⟨51,by decide⟩).lower ∧ (cell12586 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12586 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12586 ⟨52,by decide⟩).lower ∧ (cell12586 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12586 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12586 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12586 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12586,cell12586,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12586 i).lower ∧
    (cell12586 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12586 i).upper ≤ (0.532 : ℝ) ∧
    (cell12586 i).centre ≤ (0.1 : ℝ) ∧ (cell12586 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12586 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12586 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12586

/-! The local source numeric instances at 12586 have no network premises. -/
namespace BstLean.Part269.N12586
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12586)
open BstLean.Part268 (cell12586)

noncomputable def sourceNumerics12586 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12586 (cell12586 i)
      scalarRow12586.M scalarRow12586.H scalarRow12586.xi := by
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
    energy_allowance := scalarRow12586.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12586]
    centre_nonneg := (scalarRow12586.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12586])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12586
/-! Actual 12587 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12587
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12587 ≤ (1.035971017735 : ℝ) := by
  have hr : (112.191800056866 : ℝ) ≤ √(12587 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.191800056866 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12587 12587 (11 / 1000) ≤
    (0.008520115210 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12587) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.191800056866 : ℝ) ≤ √(12587 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12587)
  have hdiv : K / √(12587 : ℝ) ≤ K / 112.191800056866 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.191800056866 ≤ (0.008520115210 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12587.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12587 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12587 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12587 := gPlus_lower 12587
end BstLean.Part269.N12587

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12587
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035971017734 : ℝ) ≤ wn 12587 := by
  have hn : √(12587 : ℝ) ≤ 112.191800056867 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12587 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.191800056867 ≤ 2 / √(12587 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000254181831 : ℝ) ≤ rhoBar 12587 BstLean.Part154.csC ∧
    rhoBar 12587 BstLean.Part154.csC ≤ 0.000254182225 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035971017734 : ℝ) / (1.295212 * 12587) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035971017735 : ℝ) / (1.29521 * 12587) := by gcongr
      _ ≤ (0.000254182225 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12587 BstLean.Part154.csC) ≤ 0.001016793509 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12587 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12587 BstLean.Part154.csC) (piBar (rhoBar 12587 BstLean.Part154.csC)) ≤ 0.000194146181 ∧
    cc1 (rhoBar 12587 BstLean.Part154.csC) (piBar (rhoBar 12587 BstLean.Part154.csC)) ≤ 0.000123536487 ∧
    cc2 (rhoBar 12587 BstLean.Part154.csC) ≤ 0.000071713857 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12587 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12587 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12587 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12587 BstLean.Part154.csC * nuR (rhoBar 12587 BstLean.Part154.csC)) ≤ 0.000508380602 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000254182225 : ℝ) * 0.001016793509 := by gcongr
      _ ≤ (0.000508380602 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12587 BstLean.Part154.csC) * nuR (rhoBar 12587 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001016793509 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12587 BstLean.Part154.csC) * rhoBar 12587 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000254182225 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000254182225 / 2 + 0.399 * 0.001016793509 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000194146181 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000508380602 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123536487 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000254182225 / 1.414213562 := by gcongr
      _ ≤ (0.000071713857 : ℝ) := by norm_num

end BstLean.Part269.N12587

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12587
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12587 BstLean.Part154.csC) (piBar (rhoBar 12587 BstLean.Part154.csC)) ≤ 1.62777E-7 := by
  have hr0 : 0 ≤ rhoBar 12587 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12587 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12587 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12587 BstLean.Part154.csC) (piBar (rhoBar 12587 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12587 BstLean.Part154.csC) (piBar (rhoBar 12587 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12587 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000194146181 : ℝ) ^ 2 + 0.000123536487 ^ 2 + 3 * 0.000071713857 ^ 2 +
        2 * 0.797885 * 0.000194146181 * 0.000123536487 + 2 * 0.000194146181 * 0.000071713857 +
        4 * 0.797885 * 0.000123536487 * 0.000071713857 := by gcongr
    _ ≤ (1.62777E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12587 BstLean.Part154.csC Θ ≤ 0.002653726330 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12587 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12587 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12587 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12587 BstLean.Part154.csC) (piBar (rhoBar 12587 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12587 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035971017735 * 1.62777E-7 / (0.000254181831 : ℝ) := by gcongr
    _ ≤ 0.002653726330 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12587 BstLean.Part154.csC Θ ≤ 0.002944909737 + 0.000670552811 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12587 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12587 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12587 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035971017735 : ℝ) * ((2 * Θ * 0.000254182225 +
        (6863 / 10000) * 0.000254182225 * 12587 * 0.001016793509) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002944909737 + 0.000670552811 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12587 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12587 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12587 0.011 Θ ∧ gammaRatio 12587 0.011 Θ ≤ 0.000087381276 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12587 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035971017735 : ℝ) * 0.525 / ((1 - 0.011) * 12587) := by gcongr
      _ ≤ (0.000087381276 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12587 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12587 0.011 Θ) :=
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
    badAllowance 12587 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000674969522 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12587 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12587 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12587 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12587 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12587 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12587 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12587 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12587 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12587 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12587 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035971017735 : ℝ) * 12587 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000674969522 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12587 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003619879259 + 0.003324279141 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12587

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12587
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12587 BstLean.Part154.csC) (piBar (rhoBar 12587 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12587 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12587 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12587 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12587 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12587 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12587 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12587 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12587 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12587 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12587 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12587 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12587 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12587 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12587 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052721936109 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12587) ≤ 0.010644606651 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12587 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035971017735)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010644606651 + 2 * 0.737676 / 12587) := by gcongr
    _ ≤ (0.052721936109 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12587 12 ≤ 0.0015 := by
  exact BstLean.Part269.S9.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12587

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12587
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560498412218 : ℝ) ≤ plow 12587 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12587) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052871725809)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393206324) : eMP 12587 0.011 xi bn ≤ 0.001199257635 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12587 : ℝ) * (1 - 0.011))) ≤ 0.000592957296 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001393206324 / (12587 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000592957296 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000592957296 : ℝ) + 3.141593 * 0.052871725809 / (12587 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001199257635 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052871725809)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393206324) : PiBarMP 12587 12 0.011 xi bn ≤ 0.161980409680 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12587 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037325679150 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.573038857960 : ℝ) ≤ √((12587 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.191800056866 : ℝ) ≤ √(12587 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12587) ≤ 0.124183837462 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037325679150 + 0.052871725809 * 1.772454 / (2 * (111.573038857960 : ℝ))) * (1 + 0.001199257635) +
        8 / (12587 * 112.191800056866) + 0.124183837462 := by gcongr
    _ ≤ (0.161980409680 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052871725809)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393206324) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282660462262) :
    parallelOracle 12587 0.011 xi bn cd ≤ 0.162979739732 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12587 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12587 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560498412218 : ℝ) ≤ plow 12587 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.191800056866 : ℝ) ≤ √(12587 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282660462262 : ℝ) / (2 * 0.560498412218 * 112.191800056866)) * 0.161980409680 +
        0.282660462262 ^ 2 / (2 * 0.560498412218 * 112.191800056866) := by gcongr
    _ ≤ (0.162979739732 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052871725809) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001393206324)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282660462262) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12587 12587 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560498412218 : ℝ) ≤ plow 12587 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.191800056866 : ℝ) ≤ √(12587 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12587 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12587 Θ 1.22 ≤ 0.011819941381 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.191800056866 := by gcongr <;> linarith
      _ ≤ (0.011819941381 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12587 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12587 12587 0.011 ≤ 0.008520115210 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12587 12587 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12587 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12587 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12587 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12587 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162979739732 + 0.011819941381 + (0.008520115210 : ℝ) *
        (1 + 2 * (0.282660462262 + 0.011819941381) / (0.560498412218 * 112.191800056866))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12587]

end BstLean.Part269.N12587

/-! The original eight local profiles supply actual 12587 moment certificates. -/
namespace BstLean.Part269.N12587
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12587 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12587 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12587 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052871725809 ∧
    0 ≤ bN 12587 BstLean.Part154.csC (groupTheta g) ∧ bN 12587 BstLean.Part154.csC (groupTheta g) ≤ 0.001393206324 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12587 12587 0.011
      (momentAllowance 12587 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12587 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12587 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12587 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12587 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12587 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229938526153 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12587 0.011
      (momentAllowance 12587 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12587 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12587
/-! The actual computed-centre upper energy formula at 12587. -/
namespace BstLean.Part269.N12587
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12587

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12587
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12587)
open BstLean.Part268 (cell12587)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085826991887
  | 2 => 0.086776094002
  | 3 => 0.087724289072
  | 4 => 0.088673212807
  | 5 => 0.089624836156
  | 6 => 0.090581514115
  | 7 => 0.091546038945
  | 8 => 0.092521697809
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12587 12587 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12587 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003622837465 + 0.003327558274 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S9.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S9.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12587

/-! Actual upper energy certificates on all 43 source endpoints at 12587. -/
namespace BstLean.Part269.N12587
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12587)
open BstLean.Part268 (cell12587)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12587 (gMinus 12587) (1 - (cell12587 i).lower) ≤ 1 ∧
    energyUpper 12587 (gMinus 12587) (BstLean.Part211.gPlus 12587)
      (finiteEnergy 12587 12587 0.011) (1 - (cell12587 i).lower) ≤
      (cell12587 i).energy := by
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
      have E := BstLean.Part269.S9.uniformEnergy10 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨10,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy11 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨11,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy12 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨12,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy13 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨13,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy14 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨14,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy15 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨15,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy16 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨16,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy17 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨17,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy18 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨18,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy19 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨19,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy20 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨20,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy21 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨21,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy22 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨22,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy23 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨23,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy24 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨24,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy25 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨25,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy26 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨26,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy27 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨27,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy28 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨28,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy29 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨29,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy30 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨30,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy31 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨31,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy32 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨32,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy33 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨33,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy34 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨34,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy35 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨35,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy36 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨36,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy37 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨37,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy38 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨38,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy39 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨39,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy40 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨40,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy41 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨41,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy42 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨42,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy43 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨43,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy44 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨44,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy45 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨45,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy46 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨46,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy47 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨47,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy48 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨48,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy49 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨49,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy50 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨50,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy51 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨51,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S9.uniformEnergy52 (n := 12587) (by norm_num)
        (q := 1 - (cell12587 ⟨52,by decide⟩).lower)
        (by norm_num [cell12587]) (by norm_num [cell12587])
      exact ⟨E.1,E.2.trans (by norm_num [cell12587])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12587

/-! Source-cell containment and simple scalar guards at 12587. -/
namespace BstLean.Part269.N12587
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12587)
open BstLean.Part268 (cell12587)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12587 ⟨10,by decide⟩).lower ∧ (cell12587 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12587 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12587 ⟨11,by decide⟩).lower ∧ (cell12587 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12587 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12587 ⟨12,by decide⟩).lower ∧ (cell12587 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12587 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12587 ⟨13,by decide⟩).lower ∧ (cell12587 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12587 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12587 ⟨14,by decide⟩).lower ∧ (cell12587 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12587 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12587 ⟨15,by decide⟩).lower ∧ (cell12587 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12587 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12587 ⟨16,by decide⟩).lower ∧ (cell12587 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12587 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12587 ⟨17,by decide⟩).lower ∧ (cell12587 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12587 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12587 ⟨18,by decide⟩).lower ∧ (cell12587 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12587 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12587 ⟨19,by decide⟩).lower ∧ (cell12587 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12587 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12587 ⟨20,by decide⟩).lower ∧ (cell12587 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12587 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12587 ⟨21,by decide⟩).lower ∧ (cell12587 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12587 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12587 ⟨22,by decide⟩).lower ∧ (cell12587 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12587 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12587 ⟨23,by decide⟩).lower ∧ (cell12587 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12587 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12587 ⟨24,by decide⟩).lower ∧ (cell12587 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12587 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12587 ⟨25,by decide⟩).lower ∧ (cell12587 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12587 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12587 ⟨26,by decide⟩).lower ∧ (cell12587 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12587 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12587 ⟨27,by decide⟩).lower ∧ (cell12587 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12587 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12587 ⟨28,by decide⟩).lower ∧ (cell12587 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12587 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12587 ⟨29,by decide⟩).lower ∧ (cell12587 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12587 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12587 ⟨30,by decide⟩).lower ∧ (cell12587 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12587 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12587 ⟨31,by decide⟩).lower ∧ (cell12587 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12587 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12587 ⟨32,by decide⟩).lower ∧ (cell12587 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12587 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12587 ⟨33,by decide⟩).lower ∧ (cell12587 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12587 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12587 ⟨34,by decide⟩).lower ∧ (cell12587 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12587 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12587 ⟨35,by decide⟩).lower ∧ (cell12587 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12587 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12587 ⟨36,by decide⟩).lower ∧ (cell12587 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12587 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12587 ⟨37,by decide⟩).lower ∧ (cell12587 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12587 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12587 ⟨38,by decide⟩).lower ∧ (cell12587 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12587 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12587 ⟨39,by decide⟩).lower ∧ (cell12587 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12587 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12587 ⟨40,by decide⟩).lower ∧ (cell12587 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12587 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12587 ⟨41,by decide⟩).lower ∧ (cell12587 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12587 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12587 ⟨42,by decide⟩).lower ∧ (cell12587 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12587 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12587 ⟨43,by decide⟩).lower ∧ (cell12587 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12587 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12587 ⟨44,by decide⟩).lower ∧ (cell12587 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12587 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12587 ⟨45,by decide⟩).lower ∧ (cell12587 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12587 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12587 ⟨46,by decide⟩).lower ∧ (cell12587 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12587 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12587 ⟨47,by decide⟩).lower ∧ (cell12587 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12587 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12587 ⟨48,by decide⟩).lower ∧ (cell12587 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12587 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12587 ⟨49,by decide⟩).lower ∧ (cell12587 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12587 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12587 ⟨50,by decide⟩).lower ∧ (cell12587 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12587 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12587 ⟨51,by decide⟩).lower ∧ (cell12587 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12587 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12587 ⟨52,by decide⟩).lower ∧ (cell12587 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12587 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12587 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12587 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12587,cell12587,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12587 i).lower ∧
    (cell12587 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12587 i).upper ≤ (0.532 : ℝ) ∧
    (cell12587 i).centre ≤ (0.1 : ℝ) ∧ (cell12587 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12587 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12587 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12587

/-! The local source numeric instances at 12587 have no network premises. -/
namespace BstLean.Part269.N12587
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12587)
open BstLean.Part268 (cell12587)

noncomputable def sourceNumerics12587 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12587 (cell12587 i)
      scalarRow12587.M scalarRow12587.H scalarRow12587.xi := by
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
    energy_allowance := scalarRow12587.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12587]
    centre_nonneg := (scalarRow12587.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D9.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12587])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12587