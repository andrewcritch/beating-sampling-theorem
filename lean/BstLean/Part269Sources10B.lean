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
import BstLean.Part269Direction10
import BstLean.Part269Shared10
import BstLean.Part269Finite
import BstLean.Part269Rows10
import BstLean.Part269Source
/-! Actual 12613 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12613
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12613 ≤ (1.035933596536 : ℝ) := by
  have hr : (112.307613277106 : ℝ) ≤ √(12613 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.307613277106 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12613 12613 (11 / 1000) ≤
    (0.008511329077 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12613) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.307613277106 : ℝ) ≤ √(12613 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12613)
  have hdiv : K / √(12613 : ℝ) ≤ K / 112.307613277106 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.307613277106 ≤ (0.008511329077 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12613.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12613 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12613 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12613 := gPlus_lower 12613
end BstLean.Part269.N12613

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12613
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035933596535 : ℝ) ≤ wn 12613 := by
  have hn : √(12613 : ℝ) ≤ 112.307613277107 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12613 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.307613277107 ≤ 2 / √(12613 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253648707 : ℝ) ≤ rhoBar 12613 BstLean.Part154.csC ∧
    rhoBar 12613 BstLean.Part154.csC ≤ 0.000253649100 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035933596535 : ℝ) / (1.295212 * 12613) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035933596536 : ℝ) / (1.29521 * 12613) := by gcongr
      _ ≤ (0.000253649100 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12613 BstLean.Part154.csC) ≤ 0.001014660738 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12613 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12613 BstLean.Part154.csC) (piBar (rhoBar 12613 BstLean.Part154.csC)) ≤ 0.000193738957 ∧
    cc1 (rhoBar 12613 BstLean.Part154.csC) (piBar (rhoBar 12613 BstLean.Part154.csC)) ≤ 0.000123277372 ∧
    cc2 (rhoBar 12613 BstLean.Part154.csC) ≤ 0.000071563443 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12613 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12613 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12613 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12613 BstLean.Part154.csC * nuR (rhoBar 12613 BstLean.Part154.csC)) ≤ 0.000507314285 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253649100 : ℝ) * 0.001014660738 := by gcongr
      _ ≤ (0.000507314285 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12613 BstLean.Part154.csC) * nuR (rhoBar 12613 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001014660738 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12613 BstLean.Part154.csC) * rhoBar 12613 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253649100 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253649100 / 2 + 0.399 * 0.001014660738 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193738957 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507314285 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123277372 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253649100 / 1.414213562 := by gcongr
      _ ≤ (0.000071563443 : ℝ) := by norm_num

end BstLean.Part269.N12613

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12613
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12613 BstLean.Part154.csC) (piBar (rhoBar 12613 BstLean.Part154.csC)) ≤ 1.62095E-7 := by
  have hr0 : 0 ≤ rhoBar 12613 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12613 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12613 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12613 BstLean.Part154.csC) (piBar (rhoBar 12613 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12613 BstLean.Part154.csC) (piBar (rhoBar 12613 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12613 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193738957 : ℝ) ^ 2 + 0.000123277372 ^ 2 + 3 * 0.000071563443 ^ 2 +
        2 * 0.797885 * 0.000193738957 * 0.000123277372 + 2 * 0.000193738957 * 0.000071563443 +
        4 * 0.797885 * 0.000123277372 * 0.000071563443 := by gcongr
    _ ≤ (1.62095E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12613 BstLean.Part154.csC Θ ≤ 0.002648066428 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12613 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12613 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12613 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12613 BstLean.Part154.csC) (piBar (rhoBar 12613 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12613 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035933596536 * 1.62095E-7 / (0.000253648707 : ℝ) := by gcongr
    _ ≤ 0.002648066428 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12613 BstLean.Part154.csC Θ ≤ 0.002938520353 + 0.000669122215 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12613 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12613 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12613 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035933596536 : ℝ) * ((2 * Θ * 0.000253649100 +
        (6863 / 10000) * 0.000253649100 * 12613 * 0.001014660738) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002938520353 + 0.000669122215 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12613 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12613 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12613 0.011 Θ ∧ gammaRatio 12613 0.011 Θ ≤ 0.000087198002 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12613 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035933596536 : ℝ) * 0.525 / ((1 - 0.011) * 12613) := by gcongr
      _ ≤ (0.000087198002 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12613 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12613 0.011 Θ) :=
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
    badAllowance 12613 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12613 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12613 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12613 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12613 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12613 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12613 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12613 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12613 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12613 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12613 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035933596536 : ℝ) * 12613 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12613 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003614805749 + 0.003317188643 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12613

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12613
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12613 BstLean.Part154.csC) (piBar (rhoBar 12613 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12613 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12613 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12613 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12613 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12613 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12613 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12613 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12613 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12613 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12613 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12613 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12613 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12613 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12613 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052666976958 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12613) ≤ 0.010633629780 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12613 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035933596536)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010633629780 + 2 * 0.737676 / 12613) := by gcongr
    _ ≤ (0.052666976958 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12613 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12613

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12613
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499606754 : ℝ) ≤ plow 12613 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12613) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052862929787)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390234875) : eMP 12613 0.011 xi bn ≤ 0.001196740945 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12613 : ℝ) * (1 - 0.011))) ≤ 0.000591713811 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001390234875 / (12613 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591713811 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591713811 : ℝ) + 3.141593 * 0.052862929787 / (12613 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001196740945 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052862929787)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390234875) : PiBarMP 12613 12 0.011 xi bn ≤ 0.161811860299 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12613 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037285853551 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.688213344112 : ℝ) ≤ √((12613 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.307613277106 : ℝ) ≤ √(12613 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12613) ≤ 0.124055777309 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037285853551 + 0.052862929787 * 1.772454 / (2 * (111.688213344112 : ℝ))) * (1 + 0.001196740945) +
        8 / (12613 * 112.307613277106) + 0.124055777309 := by gcongr
    _ ≤ (0.161811860299 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052862929787)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390234875) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282586375416) :
    parallelOracle 12613 0.011 xi bn cd ≤ 0.162809351422 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12613 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12613 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499606754 : ℝ) ≤ plow 12613 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.307613277106 : ℝ) ≤ √(12613 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282586375416 : ℝ) / (2 * 0.560499606754 * 112.307613277106)) * 0.161811860299 +
        0.282586375416 ^ 2 / (2 * 0.560499606754 * 112.307613277106) := by gcongr
    _ ≤ (0.162809351422 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052862929787) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390234875)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282586375416) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12613 12613 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499606754 : ℝ) ≤ plow 12613 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.307613277106 : ℝ) ≤ √(12613 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12613 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12613 Θ 1.22 ≤ 0.011807752488 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.307613277106 := by gcongr <;> linarith
      _ ≤ (0.011807752488 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12613 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12613 12613 0.011 ≤ 0.008511329077 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12613 12613 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12613 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12613 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12613 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12613 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162809351422 + 0.011807752488 + (0.008511329077 : ℝ) *
        (1 + 2 * (0.282586375416 + 0.011807752488) / (0.560499606754 * 112.307613277106))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12613]

end BstLean.Part269.N12613

/-! The original eight local profiles supply actual 12613 moment certificates. -/
namespace BstLean.Part269.N12613
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12613 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12613 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12613 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052862929787 ∧
    0 ≤ bN 12613 BstLean.Part154.csC (groupTheta g) ∧ bN 12613 BstLean.Part154.csC (groupTheta g) ≤ 0.001390234875 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12613 12613 0.011
      (momentAllowance 12613 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12613 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12613 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12613 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12613 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12613 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229919398458 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12613 0.011
      (momentAllowance 12613 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12613 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12613
/-! The actual computed-centre upper energy formula at 12613. -/
namespace BstLean.Part269.N12613
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12613

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12613
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12613)
open BstLean.Part268 (cell12613)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085748199982
  | 2 => 0.086695785478
  | 3 => 0.087642231695
  | 4 => 0.088589121666
  | 5 => 0.089538364511
  | 6 => 0.090492243132
  | 7 => 0.091453466257
  | 8 => 0.092425224860
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12613 12613 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12613 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003617997022 + 0.003320722551 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S10.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12613

/-! Actual upper energy certificates on all 43 source endpoints at 12613. -/
namespace BstLean.Part269.N12613
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12613)
open BstLean.Part268 (cell12613)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12613 (gMinus 12613) (1 - (cell12613 i).lower) ≤ 1 ∧
    energyUpper 12613 (gMinus 12613) (BstLean.Part211.gPlus 12613)
      (finiteEnergy 12613 12613 0.011) (1 - (cell12613 i).lower) ≤
      (cell12613 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨10,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨11,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨12,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨13,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨14,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨15,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨16,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨17,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨18,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨19,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨20,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨21,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨22,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨23,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨24,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨25,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨26,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨27,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨28,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨29,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨30,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨31,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨32,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨33,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨34,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨35,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨36,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨37,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨38,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨39,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨40,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨41,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨42,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨43,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨44,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨45,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨46,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨47,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨48,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨49,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨50,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨51,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12613) (by norm_num)
        (q := 1 - (cell12613 ⟨52,by decide⟩).lower)
        (by norm_num [cell12613]) (by norm_num [cell12613])
      exact ⟨E.1,E.2.trans (by norm_num [cell12613])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12613

/-! Source-cell containment and simple scalar guards at 12613. -/
namespace BstLean.Part269.N12613
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12613)
open BstLean.Part268 (cell12613)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12613 ⟨10,by decide⟩).lower ∧ (cell12613 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12613 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12613 ⟨11,by decide⟩).lower ∧ (cell12613 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12613 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12613 ⟨12,by decide⟩).lower ∧ (cell12613 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12613 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12613 ⟨13,by decide⟩).lower ∧ (cell12613 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12613 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12613 ⟨14,by decide⟩).lower ∧ (cell12613 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12613 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12613 ⟨15,by decide⟩).lower ∧ (cell12613 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12613 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12613 ⟨16,by decide⟩).lower ∧ (cell12613 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12613 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12613 ⟨17,by decide⟩).lower ∧ (cell12613 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12613 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12613 ⟨18,by decide⟩).lower ∧ (cell12613 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12613 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12613 ⟨19,by decide⟩).lower ∧ (cell12613 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12613 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12613 ⟨20,by decide⟩).lower ∧ (cell12613 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12613 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12613 ⟨21,by decide⟩).lower ∧ (cell12613 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12613 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12613 ⟨22,by decide⟩).lower ∧ (cell12613 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12613 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12613 ⟨23,by decide⟩).lower ∧ (cell12613 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12613 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12613 ⟨24,by decide⟩).lower ∧ (cell12613 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12613 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12613 ⟨25,by decide⟩).lower ∧ (cell12613 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12613 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12613 ⟨26,by decide⟩).lower ∧ (cell12613 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12613 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12613 ⟨27,by decide⟩).lower ∧ (cell12613 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12613 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12613 ⟨28,by decide⟩).lower ∧ (cell12613 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12613 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12613 ⟨29,by decide⟩).lower ∧ (cell12613 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12613 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12613 ⟨30,by decide⟩).lower ∧ (cell12613 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12613 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12613 ⟨31,by decide⟩).lower ∧ (cell12613 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12613 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12613 ⟨32,by decide⟩).lower ∧ (cell12613 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12613 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12613 ⟨33,by decide⟩).lower ∧ (cell12613 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12613 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12613 ⟨34,by decide⟩).lower ∧ (cell12613 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12613 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12613 ⟨35,by decide⟩).lower ∧ (cell12613 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12613 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12613 ⟨36,by decide⟩).lower ∧ (cell12613 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12613 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12613 ⟨37,by decide⟩).lower ∧ (cell12613 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12613 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12613 ⟨38,by decide⟩).lower ∧ (cell12613 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12613 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12613 ⟨39,by decide⟩).lower ∧ (cell12613 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12613 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12613 ⟨40,by decide⟩).lower ∧ (cell12613 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12613 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12613 ⟨41,by decide⟩).lower ∧ (cell12613 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12613 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12613 ⟨42,by decide⟩).lower ∧ (cell12613 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12613 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12613 ⟨43,by decide⟩).lower ∧ (cell12613 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12613 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12613 ⟨44,by decide⟩).lower ∧ (cell12613 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12613 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12613 ⟨45,by decide⟩).lower ∧ (cell12613 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12613 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12613 ⟨46,by decide⟩).lower ∧ (cell12613 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12613 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12613 ⟨47,by decide⟩).lower ∧ (cell12613 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12613 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12613 ⟨48,by decide⟩).lower ∧ (cell12613 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12613 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12613 ⟨49,by decide⟩).lower ∧ (cell12613 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12613 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12613 ⟨50,by decide⟩).lower ∧ (cell12613 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12613 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12613 ⟨51,by decide⟩).lower ∧ (cell12613 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12613 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12613 ⟨52,by decide⟩).lower ∧ (cell12613 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12613 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12613 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12613 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12613,cell12613,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12613 i).lower ∧
    (cell12613 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12613 i).upper ≤ (0.532 : ℝ) ∧
    (cell12613 i).centre ≤ (0.1 : ℝ) ∧ (cell12613 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12613 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12613 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12613

/-! The local source numeric instances at 12613 have no network premises. -/
namespace BstLean.Part269.N12613
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12613)
open BstLean.Part268 (cell12613)

noncomputable def sourceNumerics12613 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12613 (cell12613 i)
      scalarRow12613.M scalarRow12613.H scalarRow12613.xi := by
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
    energy_allowance := scalarRow12613.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12613]
    centre_nonneg := (scalarRow12613.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12613])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12613
/-! Actual 12614 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12614
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12614 ≤ (1.035932159584 : ℝ) := by
  have hr : (112.312065246793 : ℝ) ≤ √(12614 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.312065246793 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12614 12614 (11 / 1000) ≤
    (0.008510991692 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12614) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.312065246793 : ℝ) ≤ √(12614 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12614)
  have hdiv : K / √(12614 : ℝ) ≤ K / 112.312065246793 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.312065246793 ≤ (0.008510991692 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12614.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12614 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12614 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12614 := gPlus_lower 12614
end BstLean.Part269.N12614

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12614
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035932159583 : ℝ) ≤ wn 12614 := by
  have hn : √(12614 : ℝ) ≤ 112.312065246794 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12614 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.312065246794 ≤ 2 / √(12614 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253628247 : ℝ) ≤ rhoBar 12614 BstLean.Part154.csC ∧
    rhoBar 12614 BstLean.Part154.csC ≤ 0.000253628640 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035932159583 : ℝ) / (1.295212 * 12614) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035932159584 : ℝ) / (1.29521 * 12614) := by gcongr
      _ ≤ (0.000253628640 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12614 BstLean.Part154.csC) ≤ 0.001014578888 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12614 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12614 BstLean.Part154.csC) (piBar (rhoBar 12614 BstLean.Part154.csC)) ≤ 0.000193723329 ∧
    cc1 (rhoBar 12614 BstLean.Part154.csC) (piBar (rhoBar 12614 BstLean.Part154.csC)) ≤ 0.000123267427 ∧
    cc2 (rhoBar 12614 BstLean.Part154.csC) ≤ 0.000071557670 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12614 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12614 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12614 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12614 BstLean.Part154.csC * nuR (rhoBar 12614 BstLean.Part154.csC)) ≤ 0.000507273362 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253628640 : ℝ) * 0.001014578888 := by gcongr
      _ ≤ (0.000507273362 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12614 BstLean.Part154.csC) * nuR (rhoBar 12614 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001014578888 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12614 BstLean.Part154.csC) * rhoBar 12614 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253628640 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253628640 / 2 + 0.399 * 0.001014578888 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193723329 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507273362 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123267427 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253628640 / 1.414213562 := by gcongr
      _ ≤ (0.000071557670 : ℝ) := by norm_num

end BstLean.Part269.N12614

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12614
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12614 BstLean.Part154.csC) (piBar (rhoBar 12614 BstLean.Part154.csC)) ≤ 1.62069E-7 := by
  have hr0 : 0 ≤ rhoBar 12614 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12614 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12614 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12614 BstLean.Part154.csC) (piBar (rhoBar 12614 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12614 BstLean.Part154.csC) (piBar (rhoBar 12614 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12614 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193723329 : ℝ) ^ 2 + 0.000123267427 ^ 2 + 3 * 0.000071557670 ^ 2 +
        2 * 0.797885 * 0.000193723329 * 0.000123267427 + 2 * 0.000193723329 * 0.000071557670 +
        4 * 0.797885 * 0.000123267427 * 0.000071557670 := by gcongr
    _ ≤ (1.62069E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12614 BstLean.Part154.csC Θ ≤ 0.002647851589 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12614 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12614 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12614 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12614 BstLean.Part154.csC) (piBar (rhoBar 12614 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12614 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035932159584 * 1.62069E-7 / (0.000253628247 : ℝ) := by gcongr
    _ ≤ 0.002647851589 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12614 BstLean.Part154.csC Θ ≤ 0.002938275163 + 0.000669067314 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12614 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12614 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12614 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035932159584 : ℝ) * ((2 * Θ * 0.000253628640 +
        (6863 / 10000) * 0.000253628640 * 12614 * 0.001014578888) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002938275163 + 0.000669067314 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12614 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12614 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12614 0.011 Θ ∧ gammaRatio 12614 0.011 Θ ≤ 0.000087190968 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12614 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035932159584 : ℝ) * 0.525 / ((1 - 0.011) * 12614) := by gcongr
      _ ≤ (0.000087190968 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12614 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12614 0.011 Θ) :=
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
    badAllowance 12614 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12614 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12614 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12614 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12614 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12614 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12614 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12614 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12614 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12614 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12614 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035932159584 : ℝ) * 12614 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12614 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003614560559 + 0.003316918903 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12614

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12614
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12614 BstLean.Part154.csC) (piBar (rhoBar 12614 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12614 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12614 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12614 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12614 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12614 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12614 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12614 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12614 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12614 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12614 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12614 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12614 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12614 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12614 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052664866565 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12614) ≤ 0.010633208271 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12614 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035932159584)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010633208271 + 2 * 0.737676 / 12614) := by gcongr
    _ ≤ (0.052664866565 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12614 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12614

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12614
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499652600 : ℝ) ≤ plow 12614 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12614) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052862542984)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390122085) : eMP 12614 0.011 xi bn ≤ 0.001196644878 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12614 : ℝ) * (1 - 0.011))) ≤ 0.000591666354 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001390122085 / (12614 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591666354 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591666354 : ℝ) + 3.141593 * 0.052862542984 / (12614 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001196644878 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052862542984)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390122085) : PiBarMP 12614 12 0.011 xi bn ≤ 0.161805404460 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12614 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037284341017 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.692640760257 : ℝ) ≤ √((12614 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.312065246793 : ℝ) ≤ √(12614 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12614) ≤ 0.124050859827 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037284341017 + 0.052862542984 * 1.772454 / (2 * (111.692640760257 : ℝ))) * (1 + 0.001196644878) +
        8 / (12614 * 112.312065246793) + 0.124050859827 := by gcongr
    _ ≤ (0.161805404460 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052862542984)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390122085) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282583423850) :
    parallelOracle 12614 0.011 xi bn cd ≤ 0.162802824429 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12614 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12614 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499652600 : ℝ) ≤ plow 12614 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.312065246793 : ℝ) ≤ √(12614 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282583423850 : ℝ) / (2 * 0.560499652600 * 112.312065246793)) * 0.161805404460 +
        0.282583423850 ^ 2 / (2 * 0.560499652600 * 112.312065246793) := by gcongr
    _ ≤ (0.162802824429 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052862542984) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390122085)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282583423850) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12614 12614 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499652600 : ℝ) ≤ plow 12614 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.312065246793 : ℝ) ≤ √(12614 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12614 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12614 Θ 1.22 ≤ 0.011807284437 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.312065246793 := by gcongr <;> linarith
      _ ≤ (0.011807284437 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12614 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12614 12614 0.011 ≤ 0.008510991692 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12614 12614 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12614 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12614 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12614 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12614 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162802824429 + 0.011807284437 + (0.008510991692 : ℝ) *
        (1 + 2 * (0.282583423850 + 0.011807284437) / (0.560499652600 * 112.312065246793))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12614]

end BstLean.Part269.N12614

/-! The original eight local profiles supply actual 12614 moment certificates. -/
namespace BstLean.Part269.N12614
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12614 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12614 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12614 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052862542984 ∧
    0 ≤ bN 12614 BstLean.Part154.csC (groupTheta g) ∧ bN 12614 BstLean.Part154.csC (groupTheta g) ≤ 0.001390122085 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12614 12614 0.011
      (momentAllowance 12614 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12614 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12614 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12614 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12614 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12614 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229918557285 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12614 0.011
      (momentAllowance 12614 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12614 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12614
/-! The actual computed-centre upper energy formula at 12614. -/
namespace BstLean.Part269.N12614
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12614

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12614
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12614)
open BstLean.Part268 (cell12614)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085745185661
  | 2 => 0.086692713506
  | 3 => 0.087639093298
  | 4 => 0.088585906079
  | 5 => 0.089535058626
  | 6 => 0.090488831109
  | 7 => 0.091449929093
  | 8 => 0.092421539906
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12614 12614 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12614 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003617997022 + 0.003320722551 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S10.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12614

/-! Actual upper energy certificates on all 43 source endpoints at 12614. -/
namespace BstLean.Part269.N12614
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12614)
open BstLean.Part268 (cell12614)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12614 (gMinus 12614) (1 - (cell12614 i).lower) ≤ 1 ∧
    energyUpper 12614 (gMinus 12614) (BstLean.Part211.gPlus 12614)
      (finiteEnergy 12614 12614 0.011) (1 - (cell12614 i).lower) ≤
      (cell12614 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨10,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨11,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨12,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨13,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨14,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨15,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨16,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨17,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨18,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨19,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨20,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨21,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨22,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨23,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨24,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨25,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨26,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨27,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨28,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨29,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨30,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨31,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨32,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨33,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨34,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨35,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨36,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨37,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨38,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨39,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨40,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨41,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨42,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨43,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨44,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨45,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨46,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨47,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨48,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨49,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨50,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨51,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12614) (by norm_num)
        (q := 1 - (cell12614 ⟨52,by decide⟩).lower)
        (by norm_num [cell12614]) (by norm_num [cell12614])
      exact ⟨E.1,E.2.trans (by norm_num [cell12614])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12614

/-! Source-cell containment and simple scalar guards at 12614. -/
namespace BstLean.Part269.N12614
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12614)
open BstLean.Part268 (cell12614)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12614 ⟨10,by decide⟩).lower ∧ (cell12614 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12614 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12614 ⟨11,by decide⟩).lower ∧ (cell12614 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12614 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12614 ⟨12,by decide⟩).lower ∧ (cell12614 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12614 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12614 ⟨13,by decide⟩).lower ∧ (cell12614 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12614 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12614 ⟨14,by decide⟩).lower ∧ (cell12614 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12614 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12614 ⟨15,by decide⟩).lower ∧ (cell12614 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12614 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12614 ⟨16,by decide⟩).lower ∧ (cell12614 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12614 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12614 ⟨17,by decide⟩).lower ∧ (cell12614 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12614 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12614 ⟨18,by decide⟩).lower ∧ (cell12614 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12614 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12614 ⟨19,by decide⟩).lower ∧ (cell12614 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12614 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12614 ⟨20,by decide⟩).lower ∧ (cell12614 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12614 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12614 ⟨21,by decide⟩).lower ∧ (cell12614 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12614 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12614 ⟨22,by decide⟩).lower ∧ (cell12614 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12614 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12614 ⟨23,by decide⟩).lower ∧ (cell12614 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12614 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12614 ⟨24,by decide⟩).lower ∧ (cell12614 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12614 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12614 ⟨25,by decide⟩).lower ∧ (cell12614 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12614 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12614 ⟨26,by decide⟩).lower ∧ (cell12614 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12614 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12614 ⟨27,by decide⟩).lower ∧ (cell12614 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12614 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12614 ⟨28,by decide⟩).lower ∧ (cell12614 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12614 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12614 ⟨29,by decide⟩).lower ∧ (cell12614 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12614 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12614 ⟨30,by decide⟩).lower ∧ (cell12614 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12614 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12614 ⟨31,by decide⟩).lower ∧ (cell12614 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12614 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12614 ⟨32,by decide⟩).lower ∧ (cell12614 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12614 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12614 ⟨33,by decide⟩).lower ∧ (cell12614 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12614 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12614 ⟨34,by decide⟩).lower ∧ (cell12614 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12614 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12614 ⟨35,by decide⟩).lower ∧ (cell12614 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12614 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12614 ⟨36,by decide⟩).lower ∧ (cell12614 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12614 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12614 ⟨37,by decide⟩).lower ∧ (cell12614 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12614 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12614 ⟨38,by decide⟩).lower ∧ (cell12614 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12614 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12614 ⟨39,by decide⟩).lower ∧ (cell12614 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12614 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12614 ⟨40,by decide⟩).lower ∧ (cell12614 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12614 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12614 ⟨41,by decide⟩).lower ∧ (cell12614 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12614 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12614 ⟨42,by decide⟩).lower ∧ (cell12614 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12614 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12614 ⟨43,by decide⟩).lower ∧ (cell12614 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12614 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12614 ⟨44,by decide⟩).lower ∧ (cell12614 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12614 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12614 ⟨45,by decide⟩).lower ∧ (cell12614 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12614 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12614 ⟨46,by decide⟩).lower ∧ (cell12614 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12614 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12614 ⟨47,by decide⟩).lower ∧ (cell12614 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12614 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12614 ⟨48,by decide⟩).lower ∧ (cell12614 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12614 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12614 ⟨49,by decide⟩).lower ∧ (cell12614 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12614 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12614 ⟨50,by decide⟩).lower ∧ (cell12614 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12614 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12614 ⟨51,by decide⟩).lower ∧ (cell12614 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12614 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12614 ⟨52,by decide⟩).lower ∧ (cell12614 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12614 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12614 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12614 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12614,cell12614,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12614 i).lower ∧
    (cell12614 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12614 i).upper ≤ (0.532 : ℝ) ∧
    (cell12614 i).centre ≤ (0.1 : ℝ) ∧ (cell12614 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12614 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12614 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12614

/-! The local source numeric instances at 12614 have no network premises. -/
namespace BstLean.Part269.N12614
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12614)
open BstLean.Part268 (cell12614)

noncomputable def sourceNumerics12614 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12614 (cell12614 i)
      scalarRow12614.M scalarRow12614.H scalarRow12614.xi := by
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
    energy_allowance := scalarRow12614.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12614]
    centre_nonneg := (scalarRow12614.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12614])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12614
/-! Actual 12615 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12615
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12615 ≤ (1.035930722804 : ℝ) := by
  have hr : (112.316517040015 : ℝ) ≤ √(12615 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.316517040015 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12615 12615 (11 / 1000) ≤
    (0.008510654346 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12615) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.316517040015 : ℝ) ≤ √(12615 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12615)
  have hdiv : K / √(12615 : ℝ) ≤ K / 112.316517040015 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.316517040015 ≤ (0.008510654346 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12615.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12615 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12615 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12615 := gPlus_lower 12615
end BstLean.Part269.N12615

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12615
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035930722803 : ℝ) ≤ wn 12615 := by
  have hn : √(12615 : ℝ) ≤ 112.316517040016 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12615 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.316517040016 ≤ 2 / √(12615 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253607790 : ℝ) ≤ rhoBar 12615 BstLean.Part154.csC ∧
    rhoBar 12615 BstLean.Part154.csC ≤ 0.000253608183 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035930722803 : ℝ) / (1.295212 * 12615) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035930722804 : ℝ) / (1.29521 * 12615) := by gcongr
      _ ≤ (0.000253608183 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12615 BstLean.Part154.csC) ≤ 0.001014497050 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12615 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12615 BstLean.Part154.csC) (piBar (rhoBar 12615 BstLean.Part154.csC)) ≤ 0.000193707703 ∧
    cc1 (rhoBar 12615 BstLean.Part154.csC) (piBar (rhoBar 12615 BstLean.Part154.csC)) ≤ 0.000123257485 ∧
    cc2 (rhoBar 12615 BstLean.Part154.csC) ≤ 0.000071551899 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12615 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12615 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12615 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12615 BstLean.Part154.csC * nuR (rhoBar 12615 BstLean.Part154.csC)) ≤ 0.000507232446 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253608183 : ℝ) * 0.001014497050 := by gcongr
      _ ≤ (0.000507232446 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12615 BstLean.Part154.csC) * nuR (rhoBar 12615 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001014497050 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12615 BstLean.Part154.csC) * rhoBar 12615 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253608183 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253608183 / 2 + 0.399 * 0.001014497050 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193707703 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507232446 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123257485 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253608183 / 1.414213562 := by gcongr
      _ ≤ (0.000071551899 : ℝ) := by norm_num

end BstLean.Part269.N12615

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12615
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12615 BstLean.Part154.csC) (piBar (rhoBar 12615 BstLean.Part154.csC)) ≤ 1.62043E-7 := by
  have hr0 : 0 ≤ rhoBar 12615 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12615 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12615 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12615 BstLean.Part154.csC) (piBar (rhoBar 12615 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12615 BstLean.Part154.csC) (piBar (rhoBar 12615 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12615 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193707703 : ℝ) ^ 2 + 0.000123257485 ^ 2 + 3 * 0.000071551899 ^ 2 +
        2 * 0.797885 * 0.000193707703 * 0.000123257485 + 2 * 0.000193707703 * 0.000071551899 +
        4 * 0.797885 * 0.000123257485 * 0.000071551899 := by gcongr
    _ ≤ (1.62043E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12615 BstLean.Part154.csC Θ ≤ 0.002647636686 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12615 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12615 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12615 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12615 BstLean.Part154.csC) (piBar (rhoBar 12615 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12615 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035930722804 * 1.62043E-7 / (0.000253607790 : ℝ) := by gcongr
    _ ≤ 0.002647636686 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12615 BstLean.Part154.csC Θ ≤ 0.002938030007 + 0.000669012421 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12615 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12615 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12615 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035930722804 : ℝ) * ((2 * Θ * 0.000253608183 +
        (6863 / 10000) * 0.000253608183 * 12615 * 0.001014497050) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002938030007 + 0.000669012421 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12615 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12615 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12615 0.011 Θ ∧ gammaRatio 12615 0.011 Θ ≤ 0.000087183935 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12615 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035930722804 : ℝ) * 0.525 / ((1 - 0.011) * 12615) := by gcongr
      _ ≤ (0.000087183935 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12615 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12615 0.011 Θ) :=
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
    badAllowance 12615 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12615 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12615 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12615 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12615 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12615 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12615 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12615 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12615 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12615 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12615 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035930722804 : ℝ) * 12615 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12615 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003614315403 + 0.003316649107 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12615

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12615
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12615 BstLean.Part154.csC) (piBar (rhoBar 12615 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12615 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12615 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12615 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12615 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12615 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12615 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12615 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12615 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12615 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12615 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12615 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12615 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12615 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12615 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052662756424 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12615) ≤ 0.010632786812 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12615 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035930722804)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010632786812 + 2 * 0.737676 / 12615) := by gcongr
    _ ≤ (0.052662756424 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12615 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12615

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12615
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499698438 : ℝ) ≤ plow 12615 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12615) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052862156185)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390009261) : eMP 12615 0.011 xi bn ≤ 0.001196548804 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12615 : ℝ) * (1 - 0.011))) ≤ 0.000591618893 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001390009261 / (12615 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591618893 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591618893 : ℝ) + 3.141593 * 0.052862156185 / (12615 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001196548804 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052862156185)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390009261) : PiBarMP 12615 12 0.011 xi bn ≤ 0.161798948689 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12615 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037282827965 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.697068000910 : ℝ) ≤ √((12615 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.316517040015 : ℝ) ≤ √(12615 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12615) ≤ 0.124045942930 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037282827965 + 0.052862156185 * 1.772454 / (2 * (111.697068000910 : ℝ))) * (1 + 0.001196548804) +
        8 / (12615 * 112.316517040015) + 0.124045942930 := by gcongr
    _ ≤ (0.161798948689 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052862156185)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390009261) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282580472543) :
    parallelOracle 12615 0.011 xi bn cd ≤ 0.162796297513 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12615 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12615 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499698438 : ℝ) ≤ plow 12615 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.316517040015 : ℝ) ≤ √(12615 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282580472543 : ℝ) / (2 * 0.560499698438 * 112.316517040015)) * 0.161798948689 +
        0.282580472543 ^ 2 / (2 * 0.560499698438 * 112.316517040015) := by gcongr
    _ ≤ (0.162796297513 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052862156185) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001390009261)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282580472543) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12615 12615 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499698438 : ℝ) ≤ plow 12615 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.316517040015 : ℝ) ≤ √(12615 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12615 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12615 Θ 1.22 ≤ 0.011806816442 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.316517040015 := by gcongr <;> linarith
      _ ≤ (0.011806816442 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12615 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12615 12615 0.011 ≤ 0.008510654346 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12615 12615 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12615 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12615 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12615 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12615 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162796297513 + 0.011806816442 + (0.008510654346 : ℝ) *
        (1 + 2 * (0.282580472543 + 0.011806816442) / (0.560499698438 * 112.316517040015))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12615]

end BstLean.Part269.N12615

/-! The original eight local profiles supply actual 12615 moment certificates. -/
namespace BstLean.Part269.N12615
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12615 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12615 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12615 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052862156185 ∧
    0 ≤ bN 12615 BstLean.Part154.csC (groupTheta g) ∧ bN 12615 BstLean.Part154.csC (groupTheta g) ≤ 0.001390009261 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12615 12615 0.011
      (momentAllowance 12615 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12615 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12615 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12615 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12615 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12615 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229917716119 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12615 0.011
      (momentAllowance 12615 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12615 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12615
/-! The actual computed-centre upper energy formula at 12615. -/
namespace BstLean.Part269.N12615
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12615

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12615
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12615)
open BstLean.Part268 (cell12615)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085742172525
  | 2 => 0.086689642768
  | 3 => 0.087635956197
  | 4 => 0.088582691862
  | 5 => 0.089531754203
  | 6 => 0.090485420661
  | 7 => 0.091446393639
  | 8 => 0.092417856825
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12615 12615 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12615 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003617997022 + 0.003320722551 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S10.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12615

/-! Actual upper energy certificates on all 43 source endpoints at 12615. -/
namespace BstLean.Part269.N12615
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12615)
open BstLean.Part268 (cell12615)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12615 (gMinus 12615) (1 - (cell12615 i).lower) ≤ 1 ∧
    energyUpper 12615 (gMinus 12615) (BstLean.Part211.gPlus 12615)
      (finiteEnergy 12615 12615 0.011) (1 - (cell12615 i).lower) ≤
      (cell12615 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨10,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨11,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨12,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨13,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨14,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨15,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨16,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨17,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨18,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨19,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨20,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨21,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨22,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨23,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨24,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨25,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨26,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨27,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨28,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨29,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨30,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨31,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨32,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨33,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨34,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨35,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨36,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨37,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨38,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨39,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨40,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨41,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨42,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨43,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨44,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨45,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨46,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨47,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨48,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨49,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨50,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨51,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12615) (by norm_num)
        (q := 1 - (cell12615 ⟨52,by decide⟩).lower)
        (by norm_num [cell12615]) (by norm_num [cell12615])
      exact ⟨E.1,E.2.trans (by norm_num [cell12615])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12615

/-! Source-cell containment and simple scalar guards at 12615. -/
namespace BstLean.Part269.N12615
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12615)
open BstLean.Part268 (cell12615)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12615 ⟨10,by decide⟩).lower ∧ (cell12615 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12615 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12615 ⟨11,by decide⟩).lower ∧ (cell12615 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12615 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12615 ⟨12,by decide⟩).lower ∧ (cell12615 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12615 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12615 ⟨13,by decide⟩).lower ∧ (cell12615 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12615 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12615 ⟨14,by decide⟩).lower ∧ (cell12615 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12615 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12615 ⟨15,by decide⟩).lower ∧ (cell12615 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12615 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12615 ⟨16,by decide⟩).lower ∧ (cell12615 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12615 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12615 ⟨17,by decide⟩).lower ∧ (cell12615 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12615 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12615 ⟨18,by decide⟩).lower ∧ (cell12615 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12615 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12615 ⟨19,by decide⟩).lower ∧ (cell12615 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12615 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12615 ⟨20,by decide⟩).lower ∧ (cell12615 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12615 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12615 ⟨21,by decide⟩).lower ∧ (cell12615 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12615 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12615 ⟨22,by decide⟩).lower ∧ (cell12615 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12615 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12615 ⟨23,by decide⟩).lower ∧ (cell12615 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12615 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12615 ⟨24,by decide⟩).lower ∧ (cell12615 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12615 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12615 ⟨25,by decide⟩).lower ∧ (cell12615 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12615 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12615 ⟨26,by decide⟩).lower ∧ (cell12615 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12615 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12615 ⟨27,by decide⟩).lower ∧ (cell12615 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12615 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12615 ⟨28,by decide⟩).lower ∧ (cell12615 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12615 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12615 ⟨29,by decide⟩).lower ∧ (cell12615 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12615 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12615 ⟨30,by decide⟩).lower ∧ (cell12615 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12615 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12615 ⟨31,by decide⟩).lower ∧ (cell12615 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12615 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12615 ⟨32,by decide⟩).lower ∧ (cell12615 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12615 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12615 ⟨33,by decide⟩).lower ∧ (cell12615 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12615 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12615 ⟨34,by decide⟩).lower ∧ (cell12615 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12615 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12615 ⟨35,by decide⟩).lower ∧ (cell12615 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12615 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12615 ⟨36,by decide⟩).lower ∧ (cell12615 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12615 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12615 ⟨37,by decide⟩).lower ∧ (cell12615 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12615 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12615 ⟨38,by decide⟩).lower ∧ (cell12615 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12615 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12615 ⟨39,by decide⟩).lower ∧ (cell12615 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12615 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12615 ⟨40,by decide⟩).lower ∧ (cell12615 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12615 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12615 ⟨41,by decide⟩).lower ∧ (cell12615 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12615 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12615 ⟨42,by decide⟩).lower ∧ (cell12615 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12615 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12615 ⟨43,by decide⟩).lower ∧ (cell12615 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12615 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12615 ⟨44,by decide⟩).lower ∧ (cell12615 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12615 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12615 ⟨45,by decide⟩).lower ∧ (cell12615 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12615 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12615 ⟨46,by decide⟩).lower ∧ (cell12615 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12615 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12615 ⟨47,by decide⟩).lower ∧ (cell12615 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12615 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12615 ⟨48,by decide⟩).lower ∧ (cell12615 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12615 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12615 ⟨49,by decide⟩).lower ∧ (cell12615 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12615 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12615 ⟨50,by decide⟩).lower ∧ (cell12615 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12615 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12615 ⟨51,by decide⟩).lower ∧ (cell12615 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12615 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12615 ⟨52,by decide⟩).lower ∧ (cell12615 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12615 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12615 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12615 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12615,cell12615,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12615 i).lower ∧
    (cell12615 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12615 i).upper ≤ (0.532 : ℝ) ∧
    (cell12615 i).centre ≤ (0.1 : ℝ) ∧ (cell12615 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12615 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12615 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12615

/-! The local source numeric instances at 12615 have no network premises. -/
namespace BstLean.Part269.N12615
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12615)
open BstLean.Part268 (cell12615)

noncomputable def sourceNumerics12615 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12615 (cell12615 i)
      scalarRow12615.M scalarRow12615.H scalarRow12615.xi := by
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
    energy_allowance := scalarRow12615.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12615]
    centre_nonneg := (scalarRow12615.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12615])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12615
/-! Actual 12616 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12616
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12616 ≤ (1.035929286195 : ℝ) := by
  have hr : (112.320968656791 : ℝ) ≤ √(12616 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.320968656791 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12616 12616 (11 / 1000) ≤
    (0.008510317041 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12616) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.320968656791 : ℝ) ≤ √(12616 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12616)
  have hdiv : K / √(12616 : ℝ) ≤ K / 112.320968656791 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.320968656791 ≤ (0.008510317041 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12616.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12616 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12616 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12616 := gPlus_lower 12616
end BstLean.Part269.N12616

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12616
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035929286194 : ℝ) ≤ wn 12616 := by
  have hn : √(12616 : ℝ) ≤ 112.320968656792 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12616 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.320968656792 ≤ 2 / √(12616 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253587336 : ℝ) ≤ rhoBar 12616 BstLean.Part154.csC ∧
    rhoBar 12616 BstLean.Part154.csC ≤ 0.000253587729 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035929286194 : ℝ) / (1.295212 * 12616) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035929286195 : ℝ) / (1.29521 * 12616) := by gcongr
      _ ≤ (0.000253587729 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12616 BstLean.Part154.csC) ≤ 0.001014415223 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12616 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12616 BstLean.Part154.csC) (piBar (rhoBar 12616 BstLean.Part154.csC)) ≤ 0.000193692079 ∧
    cc1 (rhoBar 12616 BstLean.Part154.csC) (piBar (rhoBar 12616 BstLean.Part154.csC)) ≤ 0.000123247544 ∧
    cc2 (rhoBar 12616 BstLean.Part154.csC) ≤ 0.000071546128 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12616 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12616 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12616 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12616 BstLean.Part154.csC * nuR (rhoBar 12616 BstLean.Part154.csC)) ≤ 0.000507191535 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253587729 : ℝ) * 0.001014415223 := by gcongr
      _ ≤ (0.000507191535 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12616 BstLean.Part154.csC) * nuR (rhoBar 12616 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001014415223 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12616 BstLean.Part154.csC) * rhoBar 12616 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253587729 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253587729 / 2 + 0.399 * 0.001014415223 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193692079 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507191535 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123247544 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253587729 / 1.414213562 := by gcongr
      _ ≤ (0.000071546128 : ℝ) := by norm_num

end BstLean.Part269.N12616

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12616
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12616 BstLean.Part154.csC) (piBar (rhoBar 12616 BstLean.Part154.csC)) ≤ 1.62016E-7 := by
  have hr0 : 0 ≤ rhoBar 12616 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12616 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12616 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12616 BstLean.Part154.csC) (piBar (rhoBar 12616 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12616 BstLean.Part154.csC) (piBar (rhoBar 12616 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12616 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193692079 : ℝ) ^ 2 + 0.000123247544 ^ 2 + 3 * 0.000071546128 ^ 2 +
        2 * 0.797885 * 0.000193692079 * 0.000123247544 + 2 * 0.000193692079 * 0.000071546128 +
        4 * 0.797885 * 0.000123247544 * 0.000071546128 := by gcongr
    _ ≤ (1.62016E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12616 BstLean.Part154.csC Θ ≤ 0.002647405378 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12616 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12616 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12616 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12616 BstLean.Part154.csC) (piBar (rhoBar 12616 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12616 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035929286195 * 1.62016E-7 / (0.000253587336 : ℝ) := by gcongr
    _ ≤ 0.002647405378 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12616 BstLean.Part154.csC Θ ≤ 0.002937784881 + 0.000668957536 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12616 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12616 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12616 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035929286195 : ℝ) * ((2 * Θ * 0.000253587729 +
        (6863 / 10000) * 0.000253587729 * 12616 * 0.001014415223) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002937784881 + 0.000668957536 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12616 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12616 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12616 0.011 Θ ∧ gammaRatio 12616 0.011 Θ ≤ 0.000087176904 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12616 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035929286195 : ℝ) * 0.525 / ((1 - 0.011) * 12616) := by gcongr
      _ ≤ (0.000087176904 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12616 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12616 0.011 Θ) :=
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
    badAllowance 12616 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12616 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12616 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12616 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12616 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12616 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12616 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12616 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12616 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12616 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12616 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035929286195 : ℝ) * 12616 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12616 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003614070277 + 0.003316362914 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12616

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12616
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12616 BstLean.Part154.csC) (piBar (rhoBar 12616 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12616 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12616 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12616 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12616 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12616 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12616 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12616 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12616 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12616 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12616 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12616 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12616 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12616 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12616 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052660646531 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12616) ≤ 0.010632365402 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12616 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035929286195)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010632365402 + 2 * 0.737676 / 12616) := by gcongr
    _ ≤ (0.052660646531 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12616 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12616

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12616
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499744269 : ℝ) ≤ plow 12616 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12616) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052861760807)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389887824) : eMP 12616 0.011 xi bn ≤ 0.001196449067 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12616 : ℝ) * (1 - 0.011))) ≤ 0.000591569602 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001389887824 / (12616 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591569602 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591569602 : ℝ) + 3.141593 * 0.052861760807 / (12616 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001196449067 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052861760807)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389887824) : PiBarMP 12616 12 0.011 xi bn ≤ 0.161792377584 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12616 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037281199337 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.701495066091 : ℝ) ≤ √((12616 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.320968656791 : ℝ) ≤ √(12616 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12616) ≤ 0.124041026617 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037281199337 + 0.052861760807 * 1.772454 / (2 * (111.701495066091 : ℝ))) * (1 + 0.001196449067) +
        8 / (12616 * 112.320968656791) + 0.124041026617 := by gcongr
    _ ≤ (0.161792377584 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052861760807)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389887824) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282577502823) :
    parallelOracle 12616 0.011 xi bn cd ≤ 0.162789654905 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12616 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12616 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499744269 : ℝ) ≤ plow 12616 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.320968656791 : ℝ) ≤ √(12616 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282577502823 : ℝ) / (2 * 0.560499744269 * 112.320968656791)) * 0.161792377584 +
        0.282577502823 ^ 2 / (2 * 0.560499744269 * 112.320968656791) := by gcongr
    _ ≤ (0.162789654905 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052861760807) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389887824)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282577502823) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12616 12616 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499744269 : ℝ) ≤ plow 12616 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.320968656791 : ℝ) ≤ √(12616 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12616 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12616 Θ 1.22 ≤ 0.011806348502 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.320968656791 := by gcongr <;> linarith
      _ ≤ (0.011806348502 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12616 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12616 12616 0.011 ≤ 0.008510317041 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12616 12616 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12616 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12616 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12616 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12616 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162789654905 + 0.011806348502 + (0.008510317041 : ℝ) *
        (1 + 2 * (0.282577502823 + 0.011806348502) / (0.560499744269 * 112.320968656791))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12616]

end BstLean.Part269.N12616

/-! The original eight local profiles supply actual 12616 moment certificates. -/
namespace BstLean.Part269.N12616
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12616 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12616 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12616 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052861760807 ∧
    0 ≤ bN 12616 BstLean.Part154.csC (groupTheta g) ∧ bN 12616 BstLean.Part154.csC (groupTheta g) ≤ 0.001389887824 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12616 12616 0.011
      (momentAllowance 12616 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12616 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12616 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12616 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12616 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12616 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229916856292 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12616 0.011
      (momentAllowance 12616 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12616 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12616
/-! The actual computed-centre upper energy formula at 12616. -/
namespace BstLean.Part269.N12616
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12616

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12616
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12616)
open BstLean.Part268 (cell12616)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085739160571
  | 2 => 0.086686573261
  | 3 => 0.087632820390
  | 4 => 0.088579479015
  | 5 => 0.089528451241
  | 6 => 0.090482011785
  | 7 => 0.091442859894
  | 8 => 0.092414175615
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12616 12616 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12616 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003617997022 + 0.003320722551 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S10.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12616

/-! Actual upper energy certificates on all 43 source endpoints at 12616. -/
namespace BstLean.Part269.N12616
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12616)
open BstLean.Part268 (cell12616)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12616 (gMinus 12616) (1 - (cell12616 i).lower) ≤ 1 ∧
    energyUpper 12616 (gMinus 12616) (BstLean.Part211.gPlus 12616)
      (finiteEnergy 12616 12616 0.011) (1 - (cell12616 i).lower) ≤
      (cell12616 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨10,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨11,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨12,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨13,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨14,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨15,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨16,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨17,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨18,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨19,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨20,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨21,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨22,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨23,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨24,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨25,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨26,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨27,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨28,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨29,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨30,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨31,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨32,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨33,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨34,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨35,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨36,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨37,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨38,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨39,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨40,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨41,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨42,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨43,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨44,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨45,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨46,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨47,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨48,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨49,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨50,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨51,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12616) (by norm_num)
        (q := 1 - (cell12616 ⟨52,by decide⟩).lower)
        (by norm_num [cell12616]) (by norm_num [cell12616])
      exact ⟨E.1,E.2.trans (by norm_num [cell12616])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12616

/-! Source-cell containment and simple scalar guards at 12616. -/
namespace BstLean.Part269.N12616
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12616)
open BstLean.Part268 (cell12616)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12616 ⟨10,by decide⟩).lower ∧ (cell12616 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12616 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12616 ⟨11,by decide⟩).lower ∧ (cell12616 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12616 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12616 ⟨12,by decide⟩).lower ∧ (cell12616 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12616 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12616 ⟨13,by decide⟩).lower ∧ (cell12616 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12616 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12616 ⟨14,by decide⟩).lower ∧ (cell12616 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12616 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12616 ⟨15,by decide⟩).lower ∧ (cell12616 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12616 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12616 ⟨16,by decide⟩).lower ∧ (cell12616 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12616 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12616 ⟨17,by decide⟩).lower ∧ (cell12616 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12616 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12616 ⟨18,by decide⟩).lower ∧ (cell12616 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12616 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12616 ⟨19,by decide⟩).lower ∧ (cell12616 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12616 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12616 ⟨20,by decide⟩).lower ∧ (cell12616 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12616 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12616 ⟨21,by decide⟩).lower ∧ (cell12616 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12616 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12616 ⟨22,by decide⟩).lower ∧ (cell12616 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12616 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12616 ⟨23,by decide⟩).lower ∧ (cell12616 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12616 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12616 ⟨24,by decide⟩).lower ∧ (cell12616 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12616 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12616 ⟨25,by decide⟩).lower ∧ (cell12616 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12616 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12616 ⟨26,by decide⟩).lower ∧ (cell12616 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12616 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12616 ⟨27,by decide⟩).lower ∧ (cell12616 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12616 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12616 ⟨28,by decide⟩).lower ∧ (cell12616 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12616 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12616 ⟨29,by decide⟩).lower ∧ (cell12616 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12616 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12616 ⟨30,by decide⟩).lower ∧ (cell12616 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12616 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12616 ⟨31,by decide⟩).lower ∧ (cell12616 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12616 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12616 ⟨32,by decide⟩).lower ∧ (cell12616 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12616 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12616 ⟨33,by decide⟩).lower ∧ (cell12616 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12616 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12616 ⟨34,by decide⟩).lower ∧ (cell12616 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12616 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12616 ⟨35,by decide⟩).lower ∧ (cell12616 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12616 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12616 ⟨36,by decide⟩).lower ∧ (cell12616 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12616 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12616 ⟨37,by decide⟩).lower ∧ (cell12616 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12616 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12616 ⟨38,by decide⟩).lower ∧ (cell12616 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12616 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12616 ⟨39,by decide⟩).lower ∧ (cell12616 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12616 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12616 ⟨40,by decide⟩).lower ∧ (cell12616 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12616 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12616 ⟨41,by decide⟩).lower ∧ (cell12616 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12616 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12616 ⟨42,by decide⟩).lower ∧ (cell12616 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12616 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12616 ⟨43,by decide⟩).lower ∧ (cell12616 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12616 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12616 ⟨44,by decide⟩).lower ∧ (cell12616 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12616 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12616 ⟨45,by decide⟩).lower ∧ (cell12616 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12616 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12616 ⟨46,by decide⟩).lower ∧ (cell12616 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12616 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12616 ⟨47,by decide⟩).lower ∧ (cell12616 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12616 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12616 ⟨48,by decide⟩).lower ∧ (cell12616 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12616 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12616 ⟨49,by decide⟩).lower ∧ (cell12616 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12616 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12616 ⟨50,by decide⟩).lower ∧ (cell12616 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12616 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12616 ⟨51,by decide⟩).lower ∧ (cell12616 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12616 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12616 ⟨52,by decide⟩).lower ∧ (cell12616 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12616 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12616 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12616 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12616,cell12616,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12616 i).lower ∧
    (cell12616 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12616 i).upper ≤ (0.532 : ℝ) ∧
    (cell12616 i).centre ≤ (0.1 : ℝ) ∧ (cell12616 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12616 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12616 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12616

/-! The local source numeric instances at 12616 have no network premises. -/
namespace BstLean.Part269.N12616
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12616)
open BstLean.Part268 (cell12616)

noncomputable def sourceNumerics12616 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12616 (cell12616 i)
      scalarRow12616.M scalarRow12616.H scalarRow12616.xi := by
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
    energy_allowance := scalarRow12616.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12616]
    centre_nonneg := (scalarRow12616.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12616])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12616
/-! Actual 12617 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12617
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12617 ≤ (1.035927849758 : ℝ) := by
  have hr : (112.325420097144 : ℝ) ≤ √(12617 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.325420097144 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12617 12617 (11 / 1000) ≤
    (0.008509979775 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12617) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.325420097144 : ℝ) ≤ √(12617 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12617)
  have hdiv : K / √(12617 : ℝ) ≤ K / 112.325420097144 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.325420097144 ≤ (0.008509979775 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12617.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12617 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12617 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12617 := gPlus_lower 12617
end BstLean.Part269.N12617

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12617
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035927849757 : ℝ) ≤ wn 12617 := by
  have hn : √(12617 : ℝ) ≤ 112.325420097145 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12617 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.325420097145 ≤ 2 / √(12617 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253566886 : ℝ) ≤ rhoBar 12617 BstLean.Part154.csC ∧
    rhoBar 12617 BstLean.Part154.csC ≤ 0.000253567278 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035927849757 : ℝ) / (1.295212 * 12617) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035927849758 : ℝ) / (1.29521 * 12617) := by gcongr
      _ ≤ (0.000253567278 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12617 BstLean.Part154.csC) ≤ 0.001014333409 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12617 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12617 BstLean.Part154.csC) (piBar (rhoBar 12617 BstLean.Part154.csC)) ≤ 0.000193676458 ∧
    cc1 (rhoBar 12617 BstLean.Part154.csC) (piBar (rhoBar 12617 BstLean.Part154.csC)) ≤ 0.000123237604 ∧
    cc2 (rhoBar 12617 BstLean.Part154.csC) ≤ 0.000071540358 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12617 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12617 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12617 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12617 BstLean.Part154.csC * nuR (rhoBar 12617 BstLean.Part154.csC)) ≤ 0.000507150630 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253567278 : ℝ) * 0.001014333409 := by gcongr
      _ ≤ (0.000507150630 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12617 BstLean.Part154.csC) * nuR (rhoBar 12617 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001014333409 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12617 BstLean.Part154.csC) * rhoBar 12617 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253567278 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253567278 / 2 + 0.399 * 0.001014333409 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193676458 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507150630 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123237604 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253567278 / 1.414213562 := by gcongr
      _ ≤ (0.000071540358 : ℝ) := by norm_num

end BstLean.Part269.N12617

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12617
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12617 BstLean.Part154.csC) (piBar (rhoBar 12617 BstLean.Part154.csC)) ≤ 1.61990E-7 := by
  have hr0 : 0 ≤ rhoBar 12617 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12617 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12617 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12617 BstLean.Part154.csC) (piBar (rhoBar 12617 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12617 BstLean.Part154.csC) (piBar (rhoBar 12617 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12617 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193676458 : ℝ) ^ 2 + 0.000123237604 ^ 2 + 3 * 0.000071540358 ^ 2 +
        2 * 0.797885 * 0.000193676458 * 0.000123237604 + 2 * 0.000193676458 * 0.000071540358 +
        4 * 0.797885 * 0.000123237604 * 0.000071540358 := by gcongr
    _ ≤ (1.61990E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12617 BstLean.Part154.csC Θ ≤ 0.002647190334 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12617 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12617 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12617 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12617 BstLean.Part154.csC) (piBar (rhoBar 12617 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12617 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035927849758 * 1.61990E-7 / (0.000253566886 : ℝ) := by gcongr
    _ ≤ 0.002647190334 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12617 BstLean.Part154.csC Θ ≤ 0.002937539793 + 0.000668902659 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12617 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12617 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12617 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035927849758 : ℝ) * ((2 * Θ * 0.000253567278 +
        (6863 / 10000) * 0.000253567278 * 12617 * 0.001014333409) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002937539793 + 0.000668902659 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12617 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12617 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12617 0.011 Θ ∧ gammaRatio 12617 0.011 Θ ≤ 0.000087169873 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12617 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035927849758 : ℝ) * 0.525 / ((1 - 0.011) * 12617) := by gcongr
      _ ≤ (0.000087169873 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12617 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12617 0.011 Θ) :=
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
    badAllowance 12617 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12617 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12617 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12617 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12617 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12617 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12617 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12617 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12617 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12617 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12617 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035927849758 : ℝ) * 12617 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12617 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003613825189 + 0.003316092993 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12617

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12617
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12617 BstLean.Part154.csC) (piBar (rhoBar 12617 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12617 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12617 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12617 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12617 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12617 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12617 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12617 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12617 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12617 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12617 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12617 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12617 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12617 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12617 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052658536895 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12617) ≤ 0.010631944043 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12617 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035927849758)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010631944043 + 2 * 0.737676 / 12617) := by gcongr
    _ ≤ (0.052658536895 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12617 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12617

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12617
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499790092 : ℝ) ≤ plow 12617 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12617) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052861374011)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389774926) : eMP 12617 0.011 xi bn ≤ 0.001196352977 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12617 : ℝ) * (1 - 0.011))) ≤ 0.000591522133 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001389774926 / (12617 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591522133 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591522133 : ℝ) + 3.141593 * 0.052861374011 / (12617 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001196352977 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052861374011)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389774926) : PiBarMP 12617 12 0.011 xi bn ≤ 0.161785921866 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12617 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037279685165 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.705921955821 : ℝ) ≤ √((12617 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.325420097144 : ℝ) ≤ √(12617 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12617) ≤ 0.124036110889 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037279685165 + 0.052861374011 * 1.772454 / (2 * (111.705921955821 : ℝ))) * (1 + 0.001196352977) +
        8 / (12617 * 112.325420097144) + 0.124036110889 := by gcongr
    _ ≤ (0.161785921866 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052861374011)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389774926) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282574552021) :
    parallelOracle 12617 0.011 xi bn cd ≤ 0.162783128061 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12617 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12617 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499790092 : ℝ) ≤ plow 12617 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.325420097144 : ℝ) ≤ √(12617 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282574552021 : ℝ) / (2 * 0.560499790092 * 112.325420097144)) * 0.161785921866 +
        0.282574552021 ^ 2 / (2 * 0.560499790092 * 112.325420097144) := by gcongr
    _ ≤ (0.162783128061 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052861374011) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389774926)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282574552021) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12617 12617 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499790092 : ℝ) ≤ plow 12617 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.325420097144 : ℝ) ≤ √(12617 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12617 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12617 Θ 1.22 ≤ 0.011805880618 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.325420097144 := by gcongr <;> linarith
      _ ≤ (0.011805880618 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12617 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12617 12617 0.011 ≤ 0.008509979775 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12617 12617 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12617 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12617 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12617 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12617 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162783128061 + 0.011805880618 + (0.008509979775 : ℝ) *
        (1 + 2 * (0.282574552021 + 0.011805880618) / (0.560499790092 * 112.325420097144))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12617]

end BstLean.Part269.N12617

/-! The original eight local profiles supply actual 12617 moment certificates. -/
namespace BstLean.Part269.N12617
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12617 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12617 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12617 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052861374011 ∧
    0 ≤ bN 12617 BstLean.Part154.csC (groupTheta g) ∧ bN 12617 BstLean.Part154.csC (groupTheta g) ≤ 0.001389774926 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12617 12617 0.011
      (momentAllowance 12617 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12617 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12617 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12617 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12617 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12617 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229916015126 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12617 0.011
      (momentAllowance 12617 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12617 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12617
/-! The actual computed-centre upper energy formula at 12617. -/
namespace BstLean.Part269.N12617
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12617

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12617
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12617)
open BstLean.Part268 (cell12617)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085736149798
  | 2 => 0.086683504986
  | 3 => 0.087629685874
  | 4 => 0.088576267535
  | 5 => 0.089525149738
  | 6 => 0.090478604481
  | 7 => 0.091439327854
  | 8 => 0.092410496272
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12617 12617 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12617 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003617997022 + 0.003320722551 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S10.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12617

/-! Actual upper energy certificates on all 43 source endpoints at 12617. -/
namespace BstLean.Part269.N12617
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12617)
open BstLean.Part268 (cell12617)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12617 (gMinus 12617) (1 - (cell12617 i).lower) ≤ 1 ∧
    energyUpper 12617 (gMinus 12617) (BstLean.Part211.gPlus 12617)
      (finiteEnergy 12617 12617 0.011) (1 - (cell12617 i).lower) ≤
      (cell12617 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨10,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨11,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨12,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨13,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨14,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨15,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨16,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨17,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨18,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨19,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨20,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨21,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨22,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨23,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨24,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨25,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨26,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨27,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨28,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨29,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨30,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨31,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨32,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨33,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨34,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨35,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨36,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨37,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨38,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨39,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨40,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨41,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨42,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨43,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨44,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨45,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨46,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨47,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨48,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨49,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨50,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨51,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12617) (by norm_num)
        (q := 1 - (cell12617 ⟨52,by decide⟩).lower)
        (by norm_num [cell12617]) (by norm_num [cell12617])
      exact ⟨E.1,E.2.trans (by norm_num [cell12617])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12617

/-! Source-cell containment and simple scalar guards at 12617. -/
namespace BstLean.Part269.N12617
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12617)
open BstLean.Part268 (cell12617)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12617 ⟨10,by decide⟩).lower ∧ (cell12617 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12617 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12617 ⟨11,by decide⟩).lower ∧ (cell12617 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12617 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12617 ⟨12,by decide⟩).lower ∧ (cell12617 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12617 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12617 ⟨13,by decide⟩).lower ∧ (cell12617 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12617 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12617 ⟨14,by decide⟩).lower ∧ (cell12617 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12617 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12617 ⟨15,by decide⟩).lower ∧ (cell12617 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12617 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12617 ⟨16,by decide⟩).lower ∧ (cell12617 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12617 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12617 ⟨17,by decide⟩).lower ∧ (cell12617 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12617 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12617 ⟨18,by decide⟩).lower ∧ (cell12617 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12617 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12617 ⟨19,by decide⟩).lower ∧ (cell12617 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12617 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12617 ⟨20,by decide⟩).lower ∧ (cell12617 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12617 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12617 ⟨21,by decide⟩).lower ∧ (cell12617 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12617 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12617 ⟨22,by decide⟩).lower ∧ (cell12617 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12617 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12617 ⟨23,by decide⟩).lower ∧ (cell12617 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12617 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12617 ⟨24,by decide⟩).lower ∧ (cell12617 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12617 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12617 ⟨25,by decide⟩).lower ∧ (cell12617 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12617 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12617 ⟨26,by decide⟩).lower ∧ (cell12617 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12617 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12617 ⟨27,by decide⟩).lower ∧ (cell12617 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12617 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12617 ⟨28,by decide⟩).lower ∧ (cell12617 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12617 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12617 ⟨29,by decide⟩).lower ∧ (cell12617 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12617 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12617 ⟨30,by decide⟩).lower ∧ (cell12617 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12617 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12617 ⟨31,by decide⟩).lower ∧ (cell12617 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12617 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12617 ⟨32,by decide⟩).lower ∧ (cell12617 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12617 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12617 ⟨33,by decide⟩).lower ∧ (cell12617 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12617 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12617 ⟨34,by decide⟩).lower ∧ (cell12617 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12617 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12617 ⟨35,by decide⟩).lower ∧ (cell12617 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12617 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12617 ⟨36,by decide⟩).lower ∧ (cell12617 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12617 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12617 ⟨37,by decide⟩).lower ∧ (cell12617 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12617 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12617 ⟨38,by decide⟩).lower ∧ (cell12617 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12617 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12617 ⟨39,by decide⟩).lower ∧ (cell12617 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12617 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12617 ⟨40,by decide⟩).lower ∧ (cell12617 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12617 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12617 ⟨41,by decide⟩).lower ∧ (cell12617 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12617 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12617 ⟨42,by decide⟩).lower ∧ (cell12617 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12617 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12617 ⟨43,by decide⟩).lower ∧ (cell12617 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12617 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12617 ⟨44,by decide⟩).lower ∧ (cell12617 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12617 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12617 ⟨45,by decide⟩).lower ∧ (cell12617 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12617 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12617 ⟨46,by decide⟩).lower ∧ (cell12617 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12617 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12617 ⟨47,by decide⟩).lower ∧ (cell12617 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12617 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12617 ⟨48,by decide⟩).lower ∧ (cell12617 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12617 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12617 ⟨49,by decide⟩).lower ∧ (cell12617 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12617 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12617 ⟨50,by decide⟩).lower ∧ (cell12617 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12617 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12617 ⟨51,by decide⟩).lower ∧ (cell12617 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12617 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12617 ⟨52,by decide⟩).lower ∧ (cell12617 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12617 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12617 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12617 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12617,cell12617,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12617 i).lower ∧
    (cell12617 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12617 i).upper ≤ (0.532 : ℝ) ∧
    (cell12617 i).centre ≤ (0.1 : ℝ) ∧ (cell12617 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12617 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12617 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12617

/-! The local source numeric instances at 12617 have no network premises. -/
namespace BstLean.Part269.N12617
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12617)
open BstLean.Part268 (cell12617)

noncomputable def sourceNumerics12617 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12617 (cell12617 i)
      scalarRow12617.M scalarRow12617.H scalarRow12617.xi := by
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
    energy_allowance := scalarRow12617.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12617]
    centre_nonneg := (scalarRow12617.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12617])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12617
/-! Actual 12618 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12618
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12618 ≤ (1.035926413493 : ℝ) := by
  have hr : (112.329871361094 : ℝ) ≤ √(12618 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.329871361094 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12618 12618 (11 / 1000) ≤
    (0.008509642550 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12618) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.329871361094 : ℝ) ≤ √(12618 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12618)
  have hdiv : K / √(12618 : ℝ) ≤ K / 112.329871361094 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.329871361094 ≤ (0.008509642550 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12618.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12618 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12618 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12618 := gPlus_lower 12618
end BstLean.Part269.N12618

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12618
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035926413492 : ℝ) ≤ wn 12618 := by
  have hn : √(12618 : ℝ) ≤ 112.329871361095 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12618 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.329871361095 ≤ 2 / √(12618 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253546439 : ℝ) ≤ rhoBar 12618 BstLean.Part154.csC ∧
    rhoBar 12618 BstLean.Part154.csC ≤ 0.000253546831 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035926413492 : ℝ) / (1.295212 * 12618) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035926413493 : ℝ) / (1.29521 * 12618) := by gcongr
      _ ≤ (0.000253546831 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12618 BstLean.Part154.csC) ≤ 0.001014251610 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12618 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12618 BstLean.Part154.csC) (piBar (rhoBar 12618 BstLean.Part154.csC)) ≤ 0.000193660839 ∧
    cc1 (rhoBar 12618 BstLean.Part154.csC) (piBar (rhoBar 12618 BstLean.Part154.csC)) ≤ 0.000123227666 ∧
    cc2 (rhoBar 12618 BstLean.Part154.csC) ≤ 0.000071534589 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12618 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12618 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12618 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12618 BstLean.Part154.csC * nuR (rhoBar 12618 BstLean.Part154.csC)) ≤ 0.000507109734 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253546831 : ℝ) * 0.001014251610 := by gcongr
      _ ≤ (0.000507109734 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12618 BstLean.Part154.csC) * nuR (rhoBar 12618 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001014251610 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12618 BstLean.Part154.csC) * rhoBar 12618 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253546831 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253546831 / 2 + 0.399 * 0.001014251610 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193660839 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507109734 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123227666 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253546831 / 1.414213562 := by gcongr
      _ ≤ (0.000071534589 : ℝ) := by norm_num

end BstLean.Part269.N12618

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12618
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12618 BstLean.Part154.csC) (piBar (rhoBar 12618 BstLean.Part154.csC)) ≤ 1.61964E-7 := by
  have hr0 : 0 ≤ rhoBar 12618 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12618 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12618 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12618 BstLean.Part154.csC) (piBar (rhoBar 12618 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12618 BstLean.Part154.csC) (piBar (rhoBar 12618 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12618 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193660839 : ℝ) ^ 2 + 0.000123227666 ^ 2 + 3 * 0.000071534589 ^ 2 +
        2 * 0.797885 * 0.000193660839 * 0.000123227666 + 2 * 0.000193660839 * 0.000071534589 +
        4 * 0.797885 * 0.000123227666 * 0.000071534589 := by gcongr
    _ ≤ (1.61964E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12618 BstLean.Part154.csC Θ ≤ 0.002646975226 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12618 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12618 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12618 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12618 BstLean.Part154.csC) (piBar (rhoBar 12618 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12618 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035926413493 * 1.61964E-7 / (0.000253546439 : ℝ) := by gcongr
    _ ≤ 0.002646975226 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12618 BstLean.Part154.csC Θ ≤ 0.002937294758 + 0.000668847793 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12618 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12618 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12618 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035926413493 : ℝ) * ((2 * Θ * 0.000253546831 +
        (6863 / 10000) * 0.000253546831 * 12618 * 0.001014251610) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002937294758 + 0.000668847793 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12618 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12618 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12618 0.011 Θ ∧ gammaRatio 12618 0.011 Θ ≤ 0.000087162844 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12618 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035926413493 : ℝ) * 0.525 / ((1 - 0.011) * 12618) := by gcongr
      _ ≤ (0.000087162844 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12618 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12618 0.011 Θ) :=
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
    badAllowance 12618 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12618 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12618 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12618 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12618 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12618 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12618 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12618 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12618 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12618 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12618 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035926413493 : ℝ) * 12618 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12618 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003613580154 + 0.003315823019 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12618

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12618
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12618 BstLean.Part154.csC) (piBar (rhoBar 12618 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12618 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12618 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12618 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12618 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12618 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12618 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12618 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12618 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12618 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12618 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12618 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12618 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12618 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12618 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052656427510 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12618) ≤ 0.010631522734 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12618 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035926413493)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010631522734 + 2 * 0.737676 / 12618) := by gcongr
    _ ≤ (0.052656427510 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12618 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12618

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12618
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499835909 : ℝ) ≤ plow 12618 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12618) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052860987239)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389661994) : eMP 12618 0.011 xi bn ≤ 0.001196256879 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12618 : ℝ) * (1 - 0.011))) ≤ 0.000591474660 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001389661994 / (12618 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591474660 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591474660 : ℝ) + 3.141593 * 0.052860987239 / (12618 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001196256879 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052860987239)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389661994) : PiBarMP 12618 12 0.011 xi bn ≤ 0.161779466217 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12618 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037278170476 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.710348670120 : ℝ) ≤ √((12618 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.329871361094 : ℝ) ≤ √(12618 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12618) ≤ 0.124031195745 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037278170476 + 0.052860987239 * 1.772454 / (2 * (111.710348670120 : ℝ))) * (1 + 0.001196256879) +
        8 / (12618 * 112.329871361094) + 0.124031195745 := by gcongr
    _ ≤ (0.161779466217 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052860987239)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389661994) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282571601518) :
    parallelOracle 12618 0.011 xi bn cd ≤ 0.162776601295 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12618 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12618 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499835909 : ℝ) ≤ plow 12618 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.329871361094 : ℝ) ≤ √(12618 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282571601518 : ℝ) / (2 * 0.560499835909 * 112.329871361094)) * 0.161779466217 +
        0.282571601518 ^ 2 / (2 * 0.560499835909 * 112.329871361094) := by gcongr
    _ ≤ (0.162776601295 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052860987239) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389661994)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282571601518) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12618 12618 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499835909 : ℝ) ≤ plow 12618 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.329871361094 : ℝ) ≤ √(12618 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12618 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12618 Θ 1.22 ≤ 0.011805412790 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.329871361094 := by gcongr <;> linarith
      _ ≤ (0.011805412790 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12618 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12618 12618 0.011 ≤ 0.008509642550 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12618 12618 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12618 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12618 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12618 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12618 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162776601295 + 0.011805412790 + (0.008509642550 : ℝ) *
        (1 + 2 * (0.282571601518 + 0.011805412790) / (0.560499835909 * 112.329871361094))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12618]

end BstLean.Part269.N12618

/-! The original eight local profiles supply actual 12618 moment certificates. -/
namespace BstLean.Part269.N12618
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12618 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12618 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12618 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052860987239 ∧
    0 ≤ bN 12618 BstLean.Part154.csC (groupTheta g) ∧ bN 12618 BstLean.Part154.csC (groupTheta g) ≤ 0.001389661994 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12618 12618 0.011
      (momentAllowance 12618 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12618 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12618 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12618 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12618 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12618 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229915174008 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12618 0.011
      (momentAllowance 12618 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12618 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12618
/-! The actual computed-centre upper energy formula at 12618. -/
namespace BstLean.Part269.N12618
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12618

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12618
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12618)
open BstLean.Part268 (cell12618)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085733140205
  | 2 => 0.086680437941
  | 3 => 0.087626552650
  | 4 => 0.088573057421
  | 5 => 0.089521849693
  | 6 => 0.090475198746
  | 7 => 0.091435797519
  | 8 => 0.092406818796
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12618 12618 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12618 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003617997022 + 0.003320722551 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S10.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12618

/-! Actual upper energy certificates on all 43 source endpoints at 12618. -/
namespace BstLean.Part269.N12618
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12618)
open BstLean.Part268 (cell12618)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12618 (gMinus 12618) (1 - (cell12618 i).lower) ≤ 1 ∧
    energyUpper 12618 (gMinus 12618) (BstLean.Part211.gPlus 12618)
      (finiteEnergy 12618 12618 0.011) (1 - (cell12618 i).lower) ≤
      (cell12618 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨10,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨11,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨12,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨13,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨14,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨15,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨16,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨17,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨18,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨19,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨20,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨21,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨22,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨23,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨24,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨25,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨26,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨27,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨28,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨29,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨30,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨31,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨32,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨33,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨34,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨35,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨36,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨37,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨38,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨39,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨40,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨41,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨42,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨43,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨44,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨45,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨46,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨47,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨48,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨49,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨50,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨51,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12618) (by norm_num)
        (q := 1 - (cell12618 ⟨52,by decide⟩).lower)
        (by norm_num [cell12618]) (by norm_num [cell12618])
      exact ⟨E.1,E.2.trans (by norm_num [cell12618])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12618

/-! Source-cell containment and simple scalar guards at 12618. -/
namespace BstLean.Part269.N12618
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12618)
open BstLean.Part268 (cell12618)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12618 ⟨10,by decide⟩).lower ∧ (cell12618 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12618 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12618 ⟨11,by decide⟩).lower ∧ (cell12618 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12618 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12618 ⟨12,by decide⟩).lower ∧ (cell12618 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12618 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12618 ⟨13,by decide⟩).lower ∧ (cell12618 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12618 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12618 ⟨14,by decide⟩).lower ∧ (cell12618 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12618 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12618 ⟨15,by decide⟩).lower ∧ (cell12618 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12618 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12618 ⟨16,by decide⟩).lower ∧ (cell12618 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12618 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12618 ⟨17,by decide⟩).lower ∧ (cell12618 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12618 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12618 ⟨18,by decide⟩).lower ∧ (cell12618 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12618 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12618 ⟨19,by decide⟩).lower ∧ (cell12618 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12618 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12618 ⟨20,by decide⟩).lower ∧ (cell12618 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12618 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12618 ⟨21,by decide⟩).lower ∧ (cell12618 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12618 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12618 ⟨22,by decide⟩).lower ∧ (cell12618 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12618 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12618 ⟨23,by decide⟩).lower ∧ (cell12618 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12618 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12618 ⟨24,by decide⟩).lower ∧ (cell12618 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12618 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12618 ⟨25,by decide⟩).lower ∧ (cell12618 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12618 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12618 ⟨26,by decide⟩).lower ∧ (cell12618 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12618 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12618 ⟨27,by decide⟩).lower ∧ (cell12618 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12618 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12618 ⟨28,by decide⟩).lower ∧ (cell12618 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12618 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12618 ⟨29,by decide⟩).lower ∧ (cell12618 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12618 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12618 ⟨30,by decide⟩).lower ∧ (cell12618 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12618 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12618 ⟨31,by decide⟩).lower ∧ (cell12618 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12618 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12618 ⟨32,by decide⟩).lower ∧ (cell12618 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12618 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12618 ⟨33,by decide⟩).lower ∧ (cell12618 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12618 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12618 ⟨34,by decide⟩).lower ∧ (cell12618 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12618 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12618 ⟨35,by decide⟩).lower ∧ (cell12618 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12618 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12618 ⟨36,by decide⟩).lower ∧ (cell12618 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12618 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12618 ⟨37,by decide⟩).lower ∧ (cell12618 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12618 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12618 ⟨38,by decide⟩).lower ∧ (cell12618 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12618 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12618 ⟨39,by decide⟩).lower ∧ (cell12618 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12618 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12618 ⟨40,by decide⟩).lower ∧ (cell12618 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12618 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12618 ⟨41,by decide⟩).lower ∧ (cell12618 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12618 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12618 ⟨42,by decide⟩).lower ∧ (cell12618 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12618 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12618 ⟨43,by decide⟩).lower ∧ (cell12618 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12618 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12618 ⟨44,by decide⟩).lower ∧ (cell12618 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12618 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12618 ⟨45,by decide⟩).lower ∧ (cell12618 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12618 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12618 ⟨46,by decide⟩).lower ∧ (cell12618 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12618 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12618 ⟨47,by decide⟩).lower ∧ (cell12618 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12618 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12618 ⟨48,by decide⟩).lower ∧ (cell12618 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12618 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12618 ⟨49,by decide⟩).lower ∧ (cell12618 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12618 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12618 ⟨50,by decide⟩).lower ∧ (cell12618 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12618 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12618 ⟨51,by decide⟩).lower ∧ (cell12618 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12618 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12618 ⟨52,by decide⟩).lower ∧ (cell12618 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12618 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12618 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12618 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12618,cell12618,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12618 i).lower ∧
    (cell12618 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12618 i).upper ≤ (0.532 : ℝ) ∧
    (cell12618 i).centre ≤ (0.1 : ℝ) ∧ (cell12618 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12618 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12618 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12618

/-! The local source numeric instances at 12618 have no network premises. -/
namespace BstLean.Part269.N12618
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12618)
open BstLean.Part268 (cell12618)

noncomputable def sourceNumerics12618 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12618 (cell12618 i)
      scalarRow12618.M scalarRow12618.H scalarRow12618.xi := by
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
    energy_allowance := scalarRow12618.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12618]
    centre_nonneg := (scalarRow12618.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12618])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12618
/-! Actual 12619 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12619
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12619 ≤ (1.035924977399 : ℝ) := by
  have hr : (112.334322448662 : ℝ) ≤ √(12619 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.334322448662 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12619 12619 (11 / 1000) ≤
    (0.008509305365 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12619) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.334322448662 : ℝ) ≤ √(12619 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12619)
  have hdiv : K / √(12619 : ℝ) ≤ K / 112.334322448662 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.334322448662 ≤ (0.008509305365 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12619.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12619 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12619 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12619 := gPlus_lower 12619
end BstLean.Part269.N12619

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12619
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035924977398 : ℝ) ≤ wn 12619 := by
  have hn : √(12619 : ℝ) ≤ 112.334322448663 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12619 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.334322448663 ≤ 2 / √(12619 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253525995 : ℝ) ≤ rhoBar 12619 BstLean.Part154.csC ∧
    rhoBar 12619 BstLean.Part154.csC ≤ 0.000253526387 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035924977398 : ℝ) / (1.295212 * 12619) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035924977399 : ℝ) / (1.29521 * 12619) := by gcongr
      _ ≤ (0.000253526387 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12619 BstLean.Part154.csC) ≤ 0.001014169824 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12619 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12619 BstLean.Part154.csC) (piBar (rhoBar 12619 BstLean.Part154.csC)) ≤ 0.000193645224 ∧
    cc1 (rhoBar 12619 BstLean.Part154.csC) (piBar (rhoBar 12619 BstLean.Part154.csC)) ≤ 0.000123217729 ∧
    cc2 (rhoBar 12619 BstLean.Part154.csC) ≤ 0.000071528821 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12619 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12619 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12619 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12619 BstLean.Part154.csC * nuR (rhoBar 12619 BstLean.Part154.csC)) ≤ 0.000507068843 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253526387 : ℝ) * 0.001014169824 := by gcongr
      _ ≤ (0.000507068843 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12619 BstLean.Part154.csC) * nuR (rhoBar 12619 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001014169824 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12619 BstLean.Part154.csC) * rhoBar 12619 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253526387 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253526387 / 2 + 0.399 * 0.001014169824 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193645224 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507068843 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123217729 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253526387 / 1.414213562 := by gcongr
      _ ≤ (0.000071528821 : ℝ) := by norm_num

end BstLean.Part269.N12619

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12619
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12619 BstLean.Part154.csC) (piBar (rhoBar 12619 BstLean.Part154.csC)) ≤ 1.61938E-7 := by
  have hr0 : 0 ≤ rhoBar 12619 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12619 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12619 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12619 BstLean.Part154.csC) (piBar (rhoBar 12619 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12619 BstLean.Part154.csC) (piBar (rhoBar 12619 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12619 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193645224 : ℝ) ^ 2 + 0.000123217729 ^ 2 + 3 * 0.000071528821 ^ 2 +
        2 * 0.797885 * 0.000193645224 * 0.000123217729 + 2 * 0.000193645224 * 0.000071528821 +
        4 * 0.797885 * 0.000123217729 * 0.000071528821 := by gcongr
    _ ≤ (1.61938E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12619 BstLean.Part154.csC Θ ≤ 0.002646760053 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12619 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12619 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12619 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12619 BstLean.Part154.csC) (piBar (rhoBar 12619 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12619 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035924977399 * 1.61938E-7 / (0.000253525995 : ℝ) := by gcongr
    _ ≤ 0.002646760053 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12619 BstLean.Part154.csC Θ ≤ 0.002937049760 + 0.000668792935 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12619 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12619 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12619 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035924977399 : ℝ) * ((2 * Θ * 0.000253526387 +
        (6863 / 10000) * 0.000253526387 * 12619 * 0.001014169824) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002937049760 + 0.000668792935 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12619 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12619 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12619 0.011 Θ ∧ gammaRatio 12619 0.011 Θ ≤ 0.000087155816 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12619 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035924977399 : ℝ) * 0.525 / ((1 - 0.011) * 12619) := by gcongr
      _ ≤ (0.000087155816 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12619 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12619 0.011 Θ) :=
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
    badAllowance 12619 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12619 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12619 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12619 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12619 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12619 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12619 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12619 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12619 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12619 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12619 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035924977399 : ℝ) * 12619 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12619 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003613335156 + 0.003315552988 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12619

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12619
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12619 BstLean.Part154.csC) (piBar (rhoBar 12619 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12619 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12619 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12619 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12619 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12619 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12619 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12619 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12619 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12619 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12619 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12619 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12619 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12619 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12619 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052654318378 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12619) ≤ 0.010631101475 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12619 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035924977399)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010631101475 + 2 * 0.737676 / 12619) := by gcongr
    _ ≤ (0.052654318378 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12619 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12619

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12619
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499881718 : ℝ) ≤ plow 12619 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12619) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052860600475)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389549028) : eMP 12619 0.011 xi bn ≤ 0.001196160775 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12619 : ℝ) * (1 - 0.011))) ≤ 0.000591427184 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001389549028 / (12619 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591427184 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591427184 : ℝ) + 3.141593 * 0.052860600475 / (12619 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001196160775 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052860600475)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389549028) : PiBarMP 12619 12 0.011 xi bn ≤ 0.161773010636 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12619 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037276655269 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.714775209011 : ℝ) ≤ √((12619 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.334322448662 : ℝ) ≤ √(12619 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12619) ≤ 0.124026281186 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037276655269 + 0.052860600475 * 1.772454 / (2 * (111.714775209011 : ℝ))) * (1 + 0.001196160775) +
        8 / (12619 * 112.334322448662) + 0.124026281186 := by gcongr
    _ ≤ (0.161773010636 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052860600475)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389549028) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282568651283) :
    parallelOracle 12619 0.011 xi bn cd ≤ 0.162770074606 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12619 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12619 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499881718 : ℝ) ≤ plow 12619 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.334322448662 : ℝ) ≤ √(12619 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282568651283 : ℝ) / (2 * 0.560499881718 * 112.334322448662)) * 0.161773010636 +
        0.282568651283 ^ 2 / (2 * 0.560499881718 * 112.334322448662) := by gcongr
    _ ≤ (0.162770074606 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052860600475) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389549028)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282568651283) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12619 12619 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499881718 : ℝ) ≤ plow 12619 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.334322448662 : ℝ) ≤ √(12619 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12619 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12619 Θ 1.22 ≤ 0.011804945017 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.334322448662 := by gcongr <;> linarith
      _ ≤ (0.011804945017 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12619 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12619 12619 0.011 ≤ 0.008509305365 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12619 12619 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12619 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12619 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12619 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12619 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162770074606 + 0.011804945017 + (0.008509305365 : ℝ) *
        (1 + 2 * (0.282568651283 + 0.011804945017) / (0.560499881718 * 112.334322448662))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12619]

end BstLean.Part269.N12619

/-! The original eight local profiles supply actual 12619 moment certificates. -/
namespace BstLean.Part269.N12619
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12619 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12619 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12619 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052860600475 ∧
    0 ≤ bN 12619 BstLean.Part154.csC (groupTheta g) ∧ bN 12619 BstLean.Part154.csC (groupTheta g) ≤ 0.001389549028 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12619 12619 0.011
      (momentAllowance 12619 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12619 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12619 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12619 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12619 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12619 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229914332905 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12619 0.011
      (momentAllowance 12619 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12619 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12619
/-! The actual computed-centre upper energy formula at 12619. -/
namespace BstLean.Part269.N12619
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12619

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12619
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12619)
open BstLean.Part268 (cell12619)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085730131792
  | 2 => 0.086677372124
  | 3 => 0.087623420715
  | 4 => 0.088569848671
  | 5 => 0.089518551105
  | 6 => 0.090471794579
  | 7 => 0.091432268886
  | 8 => 0.092403143184
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12619 12619 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12619 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003617997022 + 0.003320722551 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S10.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12619

/-! Actual upper energy certificates on all 43 source endpoints at 12619. -/
namespace BstLean.Part269.N12619
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12619)
open BstLean.Part268 (cell12619)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12619 (gMinus 12619) (1 - (cell12619 i).lower) ≤ 1 ∧
    energyUpper 12619 (gMinus 12619) (BstLean.Part211.gPlus 12619)
      (finiteEnergy 12619 12619 0.011) (1 - (cell12619 i).lower) ≤
      (cell12619 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨10,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨11,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨12,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨13,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨14,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨15,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨16,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨17,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨18,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨19,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨20,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨21,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨22,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨23,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨24,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨25,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨26,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨27,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨28,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨29,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨30,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨31,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨32,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨33,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨34,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨35,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨36,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨37,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨38,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨39,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨40,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨41,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨42,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨43,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨44,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨45,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨46,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨47,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨48,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨49,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨50,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨51,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12619) (by norm_num)
        (q := 1 - (cell12619 ⟨52,by decide⟩).lower)
        (by norm_num [cell12619]) (by norm_num [cell12619])
      exact ⟨E.1,E.2.trans (by norm_num [cell12619])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12619

/-! Source-cell containment and simple scalar guards at 12619. -/
namespace BstLean.Part269.N12619
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12619)
open BstLean.Part268 (cell12619)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12619 ⟨10,by decide⟩).lower ∧ (cell12619 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12619 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12619 ⟨11,by decide⟩).lower ∧ (cell12619 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12619 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12619 ⟨12,by decide⟩).lower ∧ (cell12619 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12619 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12619 ⟨13,by decide⟩).lower ∧ (cell12619 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12619 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12619 ⟨14,by decide⟩).lower ∧ (cell12619 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12619 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12619 ⟨15,by decide⟩).lower ∧ (cell12619 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12619 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12619 ⟨16,by decide⟩).lower ∧ (cell12619 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12619 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12619 ⟨17,by decide⟩).lower ∧ (cell12619 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12619 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12619 ⟨18,by decide⟩).lower ∧ (cell12619 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12619 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12619 ⟨19,by decide⟩).lower ∧ (cell12619 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12619 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12619 ⟨20,by decide⟩).lower ∧ (cell12619 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12619 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12619 ⟨21,by decide⟩).lower ∧ (cell12619 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12619 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12619 ⟨22,by decide⟩).lower ∧ (cell12619 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12619 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12619 ⟨23,by decide⟩).lower ∧ (cell12619 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12619 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12619 ⟨24,by decide⟩).lower ∧ (cell12619 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12619 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12619 ⟨25,by decide⟩).lower ∧ (cell12619 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12619 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12619 ⟨26,by decide⟩).lower ∧ (cell12619 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12619 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12619 ⟨27,by decide⟩).lower ∧ (cell12619 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12619 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12619 ⟨28,by decide⟩).lower ∧ (cell12619 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12619 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12619 ⟨29,by decide⟩).lower ∧ (cell12619 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12619 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12619 ⟨30,by decide⟩).lower ∧ (cell12619 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12619 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12619 ⟨31,by decide⟩).lower ∧ (cell12619 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12619 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12619 ⟨32,by decide⟩).lower ∧ (cell12619 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12619 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12619 ⟨33,by decide⟩).lower ∧ (cell12619 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12619 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12619 ⟨34,by decide⟩).lower ∧ (cell12619 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12619 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12619 ⟨35,by decide⟩).lower ∧ (cell12619 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12619 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12619 ⟨36,by decide⟩).lower ∧ (cell12619 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12619 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12619 ⟨37,by decide⟩).lower ∧ (cell12619 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12619 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12619 ⟨38,by decide⟩).lower ∧ (cell12619 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12619 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12619 ⟨39,by decide⟩).lower ∧ (cell12619 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12619 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12619 ⟨40,by decide⟩).lower ∧ (cell12619 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12619 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12619 ⟨41,by decide⟩).lower ∧ (cell12619 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12619 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12619 ⟨42,by decide⟩).lower ∧ (cell12619 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12619 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12619 ⟨43,by decide⟩).lower ∧ (cell12619 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12619 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12619 ⟨44,by decide⟩).lower ∧ (cell12619 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12619 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12619 ⟨45,by decide⟩).lower ∧ (cell12619 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12619 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12619 ⟨46,by decide⟩).lower ∧ (cell12619 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12619 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12619 ⟨47,by decide⟩).lower ∧ (cell12619 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12619 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12619 ⟨48,by decide⟩).lower ∧ (cell12619 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12619 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12619 ⟨49,by decide⟩).lower ∧ (cell12619 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12619 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12619 ⟨50,by decide⟩).lower ∧ (cell12619 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12619 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12619 ⟨51,by decide⟩).lower ∧ (cell12619 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12619 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12619 ⟨52,by decide⟩).lower ∧ (cell12619 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12619 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12619 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12619 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12619,cell12619,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12619 i).lower ∧
    (cell12619 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12619 i).upper ≤ (0.532 : ℝ) ∧
    (cell12619 i).centre ≤ (0.1 : ℝ) ∧ (cell12619 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12619 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12619 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12619

/-! The local source numeric instances at 12619 have no network premises. -/
namespace BstLean.Part269.N12619
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12619)
open BstLean.Part268 (cell12619)

noncomputable def sourceNumerics12619 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12619 (cell12619 i)
      scalarRow12619.M scalarRow12619.H scalarRow12619.xi := by
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
    energy_allowance := scalarRow12619.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12619]
    centre_nonneg := (scalarRow12619.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12619])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12619
/-! Actual 12620 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12620
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12620 ≤ (1.035923541477 : ℝ) := by
  have hr : (112.338773359868 : ℝ) ≤ √(12620 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.338773359868 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12620 12620 (11 / 1000) ≤
    (0.008508968220 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12620) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.338773359868 : ℝ) ≤ √(12620 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12620)
  have hdiv : K / √(12620 : ℝ) ≤ K / 112.338773359868 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.338773359868 ≤ (0.008508968220 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12620.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12620 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12620 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12620 := gPlus_lower 12620
end BstLean.Part269.N12620

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12620
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035923541476 : ℝ) ≤ wn 12620 := by
  have hn : √(12620 : ℝ) ≤ 112.338773359869 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12620 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.338773359869 ≤ 2 / √(12620 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253505554 : ℝ) ≤ rhoBar 12620 BstLean.Part154.csC ∧
    rhoBar 12620 BstLean.Part154.csC ≤ 0.000253505946 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035923541476 : ℝ) / (1.295212 * 12620) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035923541477 : ℝ) / (1.29521 * 12620) := by gcongr
      _ ≤ (0.000253505946 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12620 BstLean.Part154.csC) ≤ 0.001014088050 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12620 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12620 BstLean.Part154.csC) (piBar (rhoBar 12620 BstLean.Part154.csC)) ≤ 0.000193629610 ∧
    cc1 (rhoBar 12620 BstLean.Part154.csC) (piBar (rhoBar 12620 BstLean.Part154.csC)) ≤ 0.000123207795 ∧
    cc2 (rhoBar 12620 BstLean.Part154.csC) ≤ 0.000071523054 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12620 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12620 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12620 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12620 BstLean.Part154.csC * nuR (rhoBar 12620 BstLean.Part154.csC)) ≤ 0.000507027959 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253505946 : ℝ) * 0.001014088050 := by gcongr
      _ ≤ (0.000507027959 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12620 BstLean.Part154.csC) * nuR (rhoBar 12620 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001014088050 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12620 BstLean.Part154.csC) * rhoBar 12620 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253505946 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253505946 / 2 + 0.399 * 0.001014088050 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193629610 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000507027959 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123207795 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253505946 / 1.414213562 := by gcongr
      _ ≤ (0.000071523054 : ℝ) := by norm_num

end BstLean.Part269.N12620

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12620
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12620 BstLean.Part154.csC) (piBar (rhoBar 12620 BstLean.Part154.csC)) ≤ 1.61912E-7 := by
  have hr0 : 0 ≤ rhoBar 12620 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12620 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12620 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12620 BstLean.Part154.csC) (piBar (rhoBar 12620 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12620 BstLean.Part154.csC) (piBar (rhoBar 12620 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12620 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193629610 : ℝ) ^ 2 + 0.000123207795 ^ 2 + 3 * 0.000071523054 ^ 2 +
        2 * 0.797885 * 0.000193629610 * 0.000123207795 + 2 * 0.000193629610 * 0.000071523054 +
        4 * 0.797885 * 0.000123207795 * 0.000071523054 := by gcongr
    _ ≤ (1.61912E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12620 BstLean.Part154.csC Θ ≤ 0.002646544817 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12620 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12620 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12620 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12620 BstLean.Part154.csC) (piBar (rhoBar 12620 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12620 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035923541477 * 1.61912E-7 / (0.000253505554 : ℝ) := by gcongr
    _ ≤ 0.002646544817 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12620 BstLean.Part154.csC Θ ≤ 0.002936804795 + 0.000668738086 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12620 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12620 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12620 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035923541477 : ℝ) * ((2 * Θ * 0.000253505946 +
        (6863 / 10000) * 0.000253505946 * 12620 * 0.001014088050) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002936804795 + 0.000668738086 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12620 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12620 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12620 0.011 Θ ∧ gammaRatio 12620 0.011 Θ ≤ 0.000087148789 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12620 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035923541477 : ℝ) * 0.525 / ((1 - 0.011) * 12620) := by gcongr
      _ ≤ (0.000087148789 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12620 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12620 0.011 Θ) :=
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
    badAllowance 12620 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12620 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12620 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12620 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12620 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12620 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12620 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12620 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12620 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12620 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12620 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035923541477 : ℝ) * 12620 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12620 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003613090191 + 0.003315282903 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12620

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12620
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12620 BstLean.Part154.csC) (piBar (rhoBar 12620 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12620 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12620 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12620 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12620 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12620 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12620 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12620 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12620 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12620 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12620 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12620 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12620 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12620 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12620 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052652209498 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12620) ≤ 0.010630680266 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12620 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035923541477)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010630680266 + 2 * 0.737676 / 12620) := by gcongr
    _ ≤ (0.052652209498 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12620 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12620

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12620
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499927519 : ℝ) ≤ plow 12620 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12620) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052860213716)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389436029) : eMP 12620 0.011 xi bn ≤ 0.001196064663 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12620 : ℝ) * (1 - 0.011))) ≤ 0.000591379704 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001389436029 / (12620 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591379704 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591379704 : ℝ) + 3.141593 * 0.052860213716 / (12620 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001196064663 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052860213716)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389436029) : PiBarMP 12620 12 0.011 xi bn ≤ 0.161766555137 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12620 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037275139558 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.719201572513 : ℝ) ≤ √((12620 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.338773359868 : ℝ) ≤ √(12620 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12620) ≤ 0.124021367210 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037275139558 + 0.052860213716 * 1.772454 / (2 * (111.719201572513 : ℝ))) * (1 + 0.001196064663) +
        8 / (12620 * 112.338773359868) + 0.124021367210 := by gcongr
    _ ≤ (0.161766555137 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052860213716)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389436029) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282565701308) :
    parallelOracle 12620 0.011 xi bn cd ≤ 0.162763548009 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12620 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12620 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499927519 : ℝ) ≤ plow 12620 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.338773359868 : ℝ) ≤ √(12620 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282565701308 : ℝ) / (2 * 0.560499927519 * 112.338773359868)) * 0.161766555137 +
        0.282565701308 ^ 2 / (2 * 0.560499927519 * 112.338773359868) := by gcongr
    _ ≤ (0.162763548009 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052860213716) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389436029)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282565701308) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12620 12620 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499927519 : ℝ) ≤ plow 12620 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.338773359868 : ℝ) ≤ √(12620 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12620 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12620 Θ 1.22 ≤ 0.011804477300 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.338773359868 := by gcongr <;> linarith
      _ ≤ (0.011804477300 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12620 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12620 12620 0.011 ≤ 0.008508968220 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12620 12620 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12620 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12620 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12620 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12620 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162763548009 + 0.011804477300 + (0.008508968220 : ℝ) *
        (1 + 2 * (0.282565701308 + 0.011804477300) / (0.560499927519 * 112.338773359868))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12620]

end BstLean.Part269.N12620

/-! The original eight local profiles supply actual 12620 moment certificates. -/
namespace BstLean.Part269.N12620
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12620 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12620 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12620 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052860213716 ∧
    0 ≤ bN 12620 BstLean.Part154.csC (groupTheta g) ∧ bN 12620 BstLean.Part154.csC (groupTheta g) ≤ 0.001389436029 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12620 12620 0.011
      (momentAllowance 12620 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12620 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12620 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12620 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12620 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12620 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229913491810 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12620 0.011
      (momentAllowance 12620 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12620 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12620
/-! The actual computed-centre upper energy formula at 12620. -/
namespace BstLean.Part269.N12620
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12620

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12620
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12620)
open BstLean.Part268 (cell12620)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085727124556
  | 2 => 0.086674307534
  | 3 => 0.087620290068
  | 4 => 0.088566641285
  | 5 => 0.089515253971
  | 6 => 0.090468391978
  | 7 => 0.091428741953
  | 8 => 0.092399469434
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12620 12620 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12620 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003617997022 + 0.003320722551 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S10.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12620

/-! Actual upper energy certificates on all 43 source endpoints at 12620. -/
namespace BstLean.Part269.N12620
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12620)
open BstLean.Part268 (cell12620)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12620 (gMinus 12620) (1 - (cell12620 i).lower) ≤ 1 ∧
    energyUpper 12620 (gMinus 12620) (BstLean.Part211.gPlus 12620)
      (finiteEnergy 12620 12620 0.011) (1 - (cell12620 i).lower) ≤
      (cell12620 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨10,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨11,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨12,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨13,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨14,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨15,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨16,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨17,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨18,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨19,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨20,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨21,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨22,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨23,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨24,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨25,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨26,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨27,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨28,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨29,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨30,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨31,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨32,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨33,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨34,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨35,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨36,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨37,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨38,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨39,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨40,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨41,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨42,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨43,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨44,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨45,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨46,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨47,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨48,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨49,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨50,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨51,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12620) (by norm_num)
        (q := 1 - (cell12620 ⟨52,by decide⟩).lower)
        (by norm_num [cell12620]) (by norm_num [cell12620])
      exact ⟨E.1,E.2.trans (by norm_num [cell12620])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12620

/-! Source-cell containment and simple scalar guards at 12620. -/
namespace BstLean.Part269.N12620
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12620)
open BstLean.Part268 (cell12620)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12620 ⟨10,by decide⟩).lower ∧ (cell12620 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12620 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12620 ⟨11,by decide⟩).lower ∧ (cell12620 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12620 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12620 ⟨12,by decide⟩).lower ∧ (cell12620 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12620 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12620 ⟨13,by decide⟩).lower ∧ (cell12620 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12620 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12620 ⟨14,by decide⟩).lower ∧ (cell12620 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12620 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12620 ⟨15,by decide⟩).lower ∧ (cell12620 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12620 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12620 ⟨16,by decide⟩).lower ∧ (cell12620 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12620 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12620 ⟨17,by decide⟩).lower ∧ (cell12620 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12620 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12620 ⟨18,by decide⟩).lower ∧ (cell12620 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12620 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12620 ⟨19,by decide⟩).lower ∧ (cell12620 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12620 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12620 ⟨20,by decide⟩).lower ∧ (cell12620 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12620 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12620 ⟨21,by decide⟩).lower ∧ (cell12620 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12620 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12620 ⟨22,by decide⟩).lower ∧ (cell12620 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12620 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12620 ⟨23,by decide⟩).lower ∧ (cell12620 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12620 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12620 ⟨24,by decide⟩).lower ∧ (cell12620 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12620 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12620 ⟨25,by decide⟩).lower ∧ (cell12620 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12620 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12620 ⟨26,by decide⟩).lower ∧ (cell12620 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12620 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12620 ⟨27,by decide⟩).lower ∧ (cell12620 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12620 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12620 ⟨28,by decide⟩).lower ∧ (cell12620 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12620 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12620 ⟨29,by decide⟩).lower ∧ (cell12620 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12620 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12620 ⟨30,by decide⟩).lower ∧ (cell12620 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12620 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12620 ⟨31,by decide⟩).lower ∧ (cell12620 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12620 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12620 ⟨32,by decide⟩).lower ∧ (cell12620 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12620 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12620 ⟨33,by decide⟩).lower ∧ (cell12620 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12620 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12620 ⟨34,by decide⟩).lower ∧ (cell12620 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12620 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12620 ⟨35,by decide⟩).lower ∧ (cell12620 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12620 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12620 ⟨36,by decide⟩).lower ∧ (cell12620 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12620 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12620 ⟨37,by decide⟩).lower ∧ (cell12620 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12620 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12620 ⟨38,by decide⟩).lower ∧ (cell12620 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12620 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12620 ⟨39,by decide⟩).lower ∧ (cell12620 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12620 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12620 ⟨40,by decide⟩).lower ∧ (cell12620 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12620 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12620 ⟨41,by decide⟩).lower ∧ (cell12620 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12620 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12620 ⟨42,by decide⟩).lower ∧ (cell12620 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12620 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12620 ⟨43,by decide⟩).lower ∧ (cell12620 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12620 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12620 ⟨44,by decide⟩).lower ∧ (cell12620 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12620 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12620 ⟨45,by decide⟩).lower ∧ (cell12620 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12620 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12620 ⟨46,by decide⟩).lower ∧ (cell12620 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12620 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12620 ⟨47,by decide⟩).lower ∧ (cell12620 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12620 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12620 ⟨48,by decide⟩).lower ∧ (cell12620 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12620 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12620 ⟨49,by decide⟩).lower ∧ (cell12620 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12620 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12620 ⟨50,by decide⟩).lower ∧ (cell12620 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12620 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12620 ⟨51,by decide⟩).lower ∧ (cell12620 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12620 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12620 ⟨52,by decide⟩).lower ∧ (cell12620 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12620 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12620 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12620 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12620,cell12620,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12620 i).lower ∧
    (cell12620 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12620 i).upper ≤ (0.532 : ℝ) ∧
    (cell12620 i).centre ≤ (0.1 : ℝ) ∧ (cell12620 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12620 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12620 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12620

/-! The local source numeric instances at 12620 have no network premises. -/
namespace BstLean.Part269.N12620
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12620)
open BstLean.Part268 (cell12620)

noncomputable def sourceNumerics12620 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12620 (cell12620 i)
      scalarRow12620.M scalarRow12620.H scalarRow12620.xi := by
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
    energy_allowance := scalarRow12620.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12620]
    centre_nonneg := (scalarRow12620.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12620])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12620
/-! Actual 12621 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12621
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12621 ≤ (1.035922105727 : ℝ) := by
  have hr : (112.343224094735 : ℝ) ≤ √(12621 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.343224094735 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12621 12621 (11 / 1000) ≤
    (0.008508631115 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12621) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.343224094735 : ℝ) ≤ √(12621 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12621)
  have hdiv : K / √(12621 : ℝ) ≤ K / 112.343224094735 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.343224094735 ≤ (0.008508631115 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12621.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12621 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12621 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12621 := gPlus_lower 12621
end BstLean.Part269.N12621

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12621
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035922105726 : ℝ) ≤ wn 12621 := by
  have hn : √(12621 : ℝ) ≤ 112.343224094736 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12621 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.343224094736 ≤ 2 / √(12621 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253485117 : ℝ) ≤ rhoBar 12621 BstLean.Part154.csC ∧
    rhoBar 12621 BstLean.Part154.csC ≤ 0.000253485509 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035922105726 : ℝ) / (1.295212 * 12621) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035922105727 : ℝ) / (1.29521 * 12621) := by gcongr
      _ ≤ (0.000253485509 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12621 BstLean.Part154.csC) ≤ 0.001014006291 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12621 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12621 BstLean.Part154.csC) (piBar (rhoBar 12621 BstLean.Part154.csC)) ≤ 0.000193613999 ∧
    cc1 (rhoBar 12621 BstLean.Part154.csC) (piBar (rhoBar 12621 BstLean.Part154.csC)) ≤ 0.000123197861 ∧
    cc2 (rhoBar 12621 BstLean.Part154.csC) ≤ 0.000071517288 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12621 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12621 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12621 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12621 BstLean.Part154.csC * nuR (rhoBar 12621 BstLean.Part154.csC)) ≤ 0.000506987082 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253485509 : ℝ) * 0.001014006291 := by gcongr
      _ ≤ (0.000506987082 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12621 BstLean.Part154.csC) * nuR (rhoBar 12621 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001014006291 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12621 BstLean.Part154.csC) * rhoBar 12621 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253485509 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253485509 / 2 + 0.399 * 0.001014006291 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193613999 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506987082 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123197861 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253485509 / 1.414213562 := by gcongr
      _ ≤ (0.000071517288 : ℝ) := by norm_num

end BstLean.Part269.N12621

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12621
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12621 BstLean.Part154.csC) (piBar (rhoBar 12621 BstLean.Part154.csC)) ≤ 1.61886E-7 := by
  have hr0 : 0 ≤ rhoBar 12621 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12621 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12621 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12621 BstLean.Part154.csC) (piBar (rhoBar 12621 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12621 BstLean.Part154.csC) (piBar (rhoBar 12621 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12621 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193613999 : ℝ) ^ 2 + 0.000123197861 ^ 2 + 3 * 0.000071517288 ^ 2 +
        2 * 0.797885 * 0.000193613999 * 0.000123197861 + 2 * 0.000193613999 * 0.000071517288 +
        4 * 0.797885 * 0.000123197861 * 0.000071517288 := by gcongr
    _ ≤ (1.61886E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12621 BstLean.Part154.csC Θ ≤ 0.002646329505 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12621 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12621 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12621 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12621 BstLean.Part154.csC) (piBar (rhoBar 12621 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12621 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035922105727 * 1.61886E-7 / (0.000253485117 : ℝ) := by gcongr
    _ ≤ 0.002646329505 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12621 BstLean.Part154.csC Θ ≤ 0.002936559885 + 0.000668683247 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12621 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12621 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12621 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035922105727 : ℝ) * ((2 * Θ * 0.000253485509 +
        (6863 / 10000) * 0.000253485509 * 12621 * 0.001014006291) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002936559885 + 0.000668683247 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12621 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12621 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12621 0.011 Θ ∧ gammaRatio 12621 0.011 Θ ≤ 0.000087141763 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12621 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035922105727 : ℝ) * 0.525 / ((1 - 0.011) * 12621) := by gcongr
      _ ≤ (0.000087141763 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12621 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12621 0.011 Θ) :=
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
    badAllowance 12621 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12621 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12621 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12621 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12621 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12621 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12621 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12621 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12621 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12621 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12621 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035922105727 : ℝ) * 12621 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12621 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003612845281 + 0.003315012752 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12621

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12621
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12621 BstLean.Part154.csC) (piBar (rhoBar 12621 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12621 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12621 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12621 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12621 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12621 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12621 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12621 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12621 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12621 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12621 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12621 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12621 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12621 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12621 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052650100875 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12621) ≤ 0.010630259108 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12621 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035922105727)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010630259108 + 2 * 0.737676 / 12621) := by gcongr
    _ ≤ (0.052650100875 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12621 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12621

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12621
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560499973314 : ℝ) ≤ plow 12621 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12621) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052859826976)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389322991) : eMP 12621 0.011 xi bn ≤ 0.001195968544 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12621 : ℝ) * (1 - 0.011))) ≤ 0.000591332220 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001389322991 / (12621 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591332220 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591332220 : ℝ) + 3.141593 * 0.052859826976 / (12621 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001195968544 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052859826976)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389322991) : PiBarMP 12621 12 0.011 xi bn ≤ 0.161760099638 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12621 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037273623261 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.723627760648 : ℝ) ≤ √((12621 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.343224094735 : ℝ) ≤ √(12621 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12621) ≤ 0.124016453819 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037273623261 + 0.052859826976 * 1.772454 / (2 * (111.723627760648 : ℝ))) * (1 + 0.001195968544) +
        8 / (12621 * 112.343224094735) + 0.124016453819 := by gcongr
    _ ≤ (0.161760099638 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052859826976)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389322991) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282562751628) :
    parallelOracle 12621 0.011 xi bn cd ≤ 0.162757021421 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12621 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12621 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560499973314 : ℝ) ≤ plow 12621 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.343224094735 : ℝ) ≤ √(12621 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282562751628 : ℝ) / (2 * 0.560499973314 * 112.343224094735)) * 0.161760099638 +
        0.282562751628 ^ 2 / (2 * 0.560499973314 * 112.343224094735) := by gcongr
    _ ≤ (0.162757021421 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052859826976) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389322991)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282562751628) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12621 12621 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560499973314 : ℝ) ≤ plow 12621 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.343224094735 : ℝ) ≤ √(12621 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12621 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12621 Θ 1.22 ≤ 0.011804009639 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.343224094735 := by gcongr <;> linarith
      _ ≤ (0.011804009639 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12621 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12621 12621 0.011 ≤ 0.008508631115 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12621 12621 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12621 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12621 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12621 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12621 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162757021421 + 0.011804009639 + (0.008508631115 : ℝ) *
        (1 + 2 * (0.282562751628 + 0.011804009639) / (0.560499973314 * 112.343224094735))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12621]

end BstLean.Part269.N12621

/-! The original eight local profiles supply actual 12621 moment certificates. -/
namespace BstLean.Part269.N12621
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12621 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12621 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12621 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052859826976 ∧
    0 ≤ bN 12621 BstLean.Part154.csC (groupTheta g) ∧ bN 12621 BstLean.Part154.csC (groupTheta g) ≤ 0.001389322991 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12621 12621 0.011
      (momentAllowance 12621 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12621 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12621 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12621 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12621 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12621 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229912650753 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12621 0.011
      (momentAllowance 12621 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12621 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12621
/-! The actual computed-centre upper energy formula at 12621. -/
namespace BstLean.Part269.N12621
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12621

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12621
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12621)
open BstLean.Part268 (cell12621)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085724118496
  | 2 => 0.086671244169
  | 3 => 0.087617160708
  | 4 => 0.088563435260
  | 5 => 0.089511958291
  | 6 => 0.090464990941
  | 7 => 0.091425216719
  | 8 => 0.092395797543
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12621 12621 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12621 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003617997022 + 0.003320722551 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S10.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12621

/-! Actual upper energy certificates on all 43 source endpoints at 12621. -/
namespace BstLean.Part269.N12621
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12621)
open BstLean.Part268 (cell12621)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12621 (gMinus 12621) (1 - (cell12621 i).lower) ≤ 1 ∧
    energyUpper 12621 (gMinus 12621) (BstLean.Part211.gPlus 12621)
      (finiteEnergy 12621 12621 0.011) (1 - (cell12621 i).lower) ≤
      (cell12621 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨10,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨11,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨12,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨13,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨14,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨15,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨16,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨17,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨18,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨19,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨20,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨21,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨22,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨23,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨24,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨25,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨26,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨27,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨28,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨29,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨30,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨31,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨32,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨33,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨34,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨35,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨36,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨37,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨38,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨39,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨40,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨41,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨42,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨43,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨44,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨45,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨46,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨47,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨48,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨49,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨50,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨51,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12621) (by norm_num)
        (q := 1 - (cell12621 ⟨52,by decide⟩).lower)
        (by norm_num [cell12621]) (by norm_num [cell12621])
      exact ⟨E.1,E.2.trans (by norm_num [cell12621])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12621

/-! Source-cell containment and simple scalar guards at 12621. -/
namespace BstLean.Part269.N12621
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12621)
open BstLean.Part268 (cell12621)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12621 ⟨10,by decide⟩).lower ∧ (cell12621 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12621 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12621 ⟨11,by decide⟩).lower ∧ (cell12621 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12621 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12621 ⟨12,by decide⟩).lower ∧ (cell12621 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12621 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12621 ⟨13,by decide⟩).lower ∧ (cell12621 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12621 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12621 ⟨14,by decide⟩).lower ∧ (cell12621 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12621 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12621 ⟨15,by decide⟩).lower ∧ (cell12621 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12621 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12621 ⟨16,by decide⟩).lower ∧ (cell12621 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12621 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12621 ⟨17,by decide⟩).lower ∧ (cell12621 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12621 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12621 ⟨18,by decide⟩).lower ∧ (cell12621 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12621 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12621 ⟨19,by decide⟩).lower ∧ (cell12621 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12621 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12621 ⟨20,by decide⟩).lower ∧ (cell12621 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12621 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12621 ⟨21,by decide⟩).lower ∧ (cell12621 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12621 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12621 ⟨22,by decide⟩).lower ∧ (cell12621 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12621 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12621 ⟨23,by decide⟩).lower ∧ (cell12621 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12621 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12621 ⟨24,by decide⟩).lower ∧ (cell12621 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12621 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12621 ⟨25,by decide⟩).lower ∧ (cell12621 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12621 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12621 ⟨26,by decide⟩).lower ∧ (cell12621 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12621 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12621 ⟨27,by decide⟩).lower ∧ (cell12621 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12621 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12621 ⟨28,by decide⟩).lower ∧ (cell12621 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12621 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12621 ⟨29,by decide⟩).lower ∧ (cell12621 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12621 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12621 ⟨30,by decide⟩).lower ∧ (cell12621 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12621 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12621 ⟨31,by decide⟩).lower ∧ (cell12621 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12621 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12621 ⟨32,by decide⟩).lower ∧ (cell12621 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12621 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12621 ⟨33,by decide⟩).lower ∧ (cell12621 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12621 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12621 ⟨34,by decide⟩).lower ∧ (cell12621 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12621 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12621 ⟨35,by decide⟩).lower ∧ (cell12621 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12621 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12621 ⟨36,by decide⟩).lower ∧ (cell12621 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12621 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12621 ⟨37,by decide⟩).lower ∧ (cell12621 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12621 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12621 ⟨38,by decide⟩).lower ∧ (cell12621 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12621 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12621 ⟨39,by decide⟩).lower ∧ (cell12621 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12621 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12621 ⟨40,by decide⟩).lower ∧ (cell12621 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12621 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12621 ⟨41,by decide⟩).lower ∧ (cell12621 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12621 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12621 ⟨42,by decide⟩).lower ∧ (cell12621 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12621 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12621 ⟨43,by decide⟩).lower ∧ (cell12621 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12621 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12621 ⟨44,by decide⟩).lower ∧ (cell12621 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12621 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12621 ⟨45,by decide⟩).lower ∧ (cell12621 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12621 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12621 ⟨46,by decide⟩).lower ∧ (cell12621 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12621 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12621 ⟨47,by decide⟩).lower ∧ (cell12621 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12621 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12621 ⟨48,by decide⟩).lower ∧ (cell12621 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12621 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12621 ⟨49,by decide⟩).lower ∧ (cell12621 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12621 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12621 ⟨50,by decide⟩).lower ∧ (cell12621 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12621 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12621 ⟨51,by decide⟩).lower ∧ (cell12621 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12621 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12621 ⟨52,by decide⟩).lower ∧ (cell12621 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12621 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12621 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12621 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12621,cell12621,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12621 i).lower ∧
    (cell12621 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12621 i).upper ≤ (0.532 : ℝ) ∧
    (cell12621 i).centre ≤ (0.1 : ℝ) ∧ (cell12621 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12621 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12621 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12621

/-! The local source numeric instances at 12621 have no network premises. -/
namespace BstLean.Part269.N12621
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12621)
open BstLean.Part268 (cell12621)

noncomputable def sourceNumerics12621 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12621 (cell12621 i)
      scalarRow12621.M scalarRow12621.H scalarRow12621.xi := by
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
    energy_allowance := scalarRow12621.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12621]
    centre_nonneg := (scalarRow12621.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12621])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12621
/-! Actual 12622 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12622
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12622 ≤ (1.035920670149 : ℝ) := by
  have hr : (112.347674653283 : ℝ) ≤ √(12622 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.347674653283 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12622 12622 (11 / 1000) ≤
    (0.008508294050 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12622) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.347674653283 : ℝ) ≤ √(12622 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12622)
  have hdiv : K / √(12622 : ℝ) ≤ K / 112.347674653283 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.347674653283 ≤ (0.008508294050 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12622.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12622 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12622 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12622 := gPlus_lower 12622
end BstLean.Part269.N12622

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12622
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035920670148 : ℝ) ≤ wn 12622 := by
  have hn : √(12622 : ℝ) ≤ 112.347674653284 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12622 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.347674653284 ≤ 2 / √(12622 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253464683 : ℝ) ≤ rhoBar 12622 BstLean.Part154.csC ∧
    rhoBar 12622 BstLean.Part154.csC ≤ 0.000253465075 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035920670148 : ℝ) / (1.295212 * 12622) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035920670149 : ℝ) / (1.29521 * 12622) := by gcongr
      _ ≤ (0.000253465075 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12622 BstLean.Part154.csC) ≤ 0.001013924545 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12622 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12622 BstLean.Part154.csC) (piBar (rhoBar 12622 BstLean.Part154.csC)) ≤ 0.000193598391 ∧
    cc1 (rhoBar 12622 BstLean.Part154.csC) (piBar (rhoBar 12622 BstLean.Part154.csC)) ≤ 0.000123187930 ∧
    cc2 (rhoBar 12622 BstLean.Part154.csC) ≤ 0.000071511523 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12622 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12622 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12622 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12622 BstLean.Part154.csC * nuR (rhoBar 12622 BstLean.Part154.csC)) ≤ 0.000506946211 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253465075 : ℝ) * 0.001013924545 := by gcongr
      _ ≤ (0.000506946211 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12622 BstLean.Part154.csC) * nuR (rhoBar 12622 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001013924545 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12622 BstLean.Part154.csC) * rhoBar 12622 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253465075 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253465075 / 2 + 0.399 * 0.001013924545 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193598391 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506946211 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123187930 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253465075 / 1.414213562 := by gcongr
      _ ≤ (0.000071511523 : ℝ) := by norm_num

end BstLean.Part269.N12622

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12622
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12622 BstLean.Part154.csC) (piBar (rhoBar 12622 BstLean.Part154.csC)) ≤ 1.61860E-7 := by
  have hr0 : 0 ≤ rhoBar 12622 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12622 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12622 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12622 BstLean.Part154.csC) (piBar (rhoBar 12622 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12622 BstLean.Part154.csC) (piBar (rhoBar 12622 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12622 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193598391 : ℝ) ^ 2 + 0.000123187930 ^ 2 + 3 * 0.000071511523 ^ 2 +
        2 * 0.797885 * 0.000193598391 * 0.000123187930 + 2 * 0.000193598391 * 0.000071511523 +
        4 * 0.797885 * 0.000123187930 * 0.000071511523 := by gcongr
    _ ≤ (1.61860E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12622 BstLean.Part154.csC Θ ≤ 0.002646114129 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12622 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12622 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12622 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12622 BstLean.Part154.csC) (piBar (rhoBar 12622 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12622 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035920670149 * 1.61860E-7 / (0.000253464683 : ℝ) := by gcongr
    _ ≤ 0.002646114129 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12622 BstLean.Part154.csC Θ ≤ 0.002936315012 + 0.000668628417 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12622 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12622 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12622 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035920670149 : ℝ) * ((2 * Θ * 0.000253465075 +
        (6863 / 10000) * 0.000253465075 * 12622 * 0.001013924545) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002936315012 + 0.000668628417 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12622 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12622 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12622 0.011 Θ ∧ gammaRatio 12622 0.011 Θ ≤ 0.000087134739 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12622 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035920670149 : ℝ) * 0.525 / ((1 - 0.011) * 12622) := by gcongr
      _ ≤ (0.000087134739 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12622 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12622 0.011 Θ) :=
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
    badAllowance 12622 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12622 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12622 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12622 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12622 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12622 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12622 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12622 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12622 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12622 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12622 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035920670149 : ℝ) * 12622 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12622 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003612600408 + 0.003314742546 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12622

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12622
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12622 BstLean.Part154.csC) (piBar (rhoBar 12622 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12622 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12622 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12622 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12622 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12622 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12622 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12622 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12622 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12622 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12622 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12622 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12622 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12622 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12622 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052647992500 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12622) ≤ 0.010629837999 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12622 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035920670149)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010629837999 + 2 * 0.737676 / 12622) := by gcongr
    _ ≤ (0.052647992500 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12622 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12622

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12622
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500019101 : ℝ) ≤ plow 12622 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12622) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052859440245)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389209918) : eMP 12622 0.011 xi bn ≤ 0.001195872416 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12622 : ℝ) * (1 - 0.011))) ≤ 0.000591284732 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001389209918 / (12622 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591284732 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591284732 : ℝ) + 3.141593 * 0.052859440245 / (12622 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001195872416 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052859440245)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389209918) : PiBarMP 12622 12 0.011 xi bn ≤ 0.161753644194 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12622 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037272106434 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.728053773436 : ℝ) ≤ √((12622 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.347674653283 : ℝ) ≤ √(12622 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12622) ≤ 0.124011541011 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037272106434 + 0.052859440245 * 1.772454 / (2 * (111.728053773436 : ℝ))) * (1 + 0.001195872416) +
        8 / (12622 * 112.347674653283) + 0.124011541011 := by gcongr
    _ ≤ (0.161753644194 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052859440245)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389209918) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282559802212) :
    parallelOracle 12622 0.011 xi bn cd ≤ 0.162750494897 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12622 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12622 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500019101 : ℝ) ≤ plow 12622 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.347674653283 : ℝ) ≤ √(12622 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282559802212 : ℝ) / (2 * 0.560500019101 * 112.347674653283)) * 0.161753644194 +
        0.282559802212 ^ 2 / (2 * 0.560500019101 * 112.347674653283) := by gcongr
    _ ≤ (0.162750494897 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052859440245) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389209918)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282559802212) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12622 12622 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500019101 : ℝ) ≤ plow 12622 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.347674653283 : ℝ) ≤ √(12622 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12622 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12622 Θ 1.22 ≤ 0.011803542033 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.347674653283 := by gcongr <;> linarith
      _ ≤ (0.011803542033 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12622 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12622 12622 0.011 ≤ 0.008508294050 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12622 12622 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12622 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12622 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12622 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12622 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162750494897 + 0.011803542033 + (0.008508294050 : ℝ) *
        (1 + 2 * (0.282559802212 + 0.011803542033) / (0.560500019101 * 112.347674653283))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12622]

end BstLean.Part269.N12622

/-! The original eight local profiles supply actual 12622 moment certificates. -/
namespace BstLean.Part269.N12622
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12622 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12622 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12622 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052859440245 ∧
    0 ≤ bN 12622 BstLean.Part154.csC (groupTheta g) ∧ bN 12622 BstLean.Part154.csC (groupTheta g) ≤ 0.001389209918 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12622 12622 0.011
      (momentAllowance 12622 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12622 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12622 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12622 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12622 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12622 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229911809712 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12622 0.011
      (momentAllowance 12622 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12622 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12622
/-! The actual computed-centre upper energy formula at 12622. -/
namespace BstLean.Part269.N12622
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12622

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12622
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12622)
open BstLean.Part268 (cell12622)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085721113612
  | 2 => 0.086668182030
  | 3 => 0.087614032633
  | 4 => 0.088560230596
  | 5 => 0.089508664062
  | 6 => 0.090461591467
  | 7 => 0.091421693181
  | 8 => 0.092392127511
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12622 12622 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12622 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003617997022 + 0.003320722551 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S10.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12622

/-! Actual upper energy certificates on all 43 source endpoints at 12622. -/
namespace BstLean.Part269.N12622
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12622)
open BstLean.Part268 (cell12622)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12622 (gMinus 12622) (1 - (cell12622 i).lower) ≤ 1 ∧
    energyUpper 12622 (gMinus 12622) (BstLean.Part211.gPlus 12622)
      (finiteEnergy 12622 12622 0.011) (1 - (cell12622 i).lower) ≤
      (cell12622 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨10,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨11,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨12,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨13,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨14,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨15,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨16,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨17,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨18,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨19,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨20,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨21,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨22,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨23,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨24,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨25,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨26,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨27,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨28,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨29,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨30,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨31,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨32,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨33,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨34,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨35,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨36,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨37,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨38,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨39,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨40,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨41,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨42,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨43,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨44,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨45,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨46,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨47,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨48,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨49,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨50,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨51,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12622) (by norm_num)
        (q := 1 - (cell12622 ⟨52,by decide⟩).lower)
        (by norm_num [cell12622]) (by norm_num [cell12622])
      exact ⟨E.1,E.2.trans (by norm_num [cell12622])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12622

/-! Source-cell containment and simple scalar guards at 12622. -/
namespace BstLean.Part269.N12622
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12622)
open BstLean.Part268 (cell12622)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12622 ⟨10,by decide⟩).lower ∧ (cell12622 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12622 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12622 ⟨11,by decide⟩).lower ∧ (cell12622 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12622 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12622 ⟨12,by decide⟩).lower ∧ (cell12622 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12622 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12622 ⟨13,by decide⟩).lower ∧ (cell12622 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12622 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12622 ⟨14,by decide⟩).lower ∧ (cell12622 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12622 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12622 ⟨15,by decide⟩).lower ∧ (cell12622 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12622 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12622 ⟨16,by decide⟩).lower ∧ (cell12622 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12622 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12622 ⟨17,by decide⟩).lower ∧ (cell12622 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12622 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12622 ⟨18,by decide⟩).lower ∧ (cell12622 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12622 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12622 ⟨19,by decide⟩).lower ∧ (cell12622 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12622 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12622 ⟨20,by decide⟩).lower ∧ (cell12622 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12622 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12622 ⟨21,by decide⟩).lower ∧ (cell12622 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12622 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12622 ⟨22,by decide⟩).lower ∧ (cell12622 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12622 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12622 ⟨23,by decide⟩).lower ∧ (cell12622 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12622 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12622 ⟨24,by decide⟩).lower ∧ (cell12622 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12622 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12622 ⟨25,by decide⟩).lower ∧ (cell12622 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12622 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12622 ⟨26,by decide⟩).lower ∧ (cell12622 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12622 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12622 ⟨27,by decide⟩).lower ∧ (cell12622 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12622 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12622 ⟨28,by decide⟩).lower ∧ (cell12622 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12622 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12622 ⟨29,by decide⟩).lower ∧ (cell12622 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12622 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12622 ⟨30,by decide⟩).lower ∧ (cell12622 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12622 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12622 ⟨31,by decide⟩).lower ∧ (cell12622 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12622 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12622 ⟨32,by decide⟩).lower ∧ (cell12622 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12622 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12622 ⟨33,by decide⟩).lower ∧ (cell12622 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12622 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12622 ⟨34,by decide⟩).lower ∧ (cell12622 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12622 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12622 ⟨35,by decide⟩).lower ∧ (cell12622 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12622 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12622 ⟨36,by decide⟩).lower ∧ (cell12622 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12622 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12622 ⟨37,by decide⟩).lower ∧ (cell12622 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12622 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12622 ⟨38,by decide⟩).lower ∧ (cell12622 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12622 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12622 ⟨39,by decide⟩).lower ∧ (cell12622 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12622 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12622 ⟨40,by decide⟩).lower ∧ (cell12622 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12622 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12622 ⟨41,by decide⟩).lower ∧ (cell12622 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12622 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12622 ⟨42,by decide⟩).lower ∧ (cell12622 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12622 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12622 ⟨43,by decide⟩).lower ∧ (cell12622 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12622 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12622 ⟨44,by decide⟩).lower ∧ (cell12622 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12622 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12622 ⟨45,by decide⟩).lower ∧ (cell12622 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12622 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12622 ⟨46,by decide⟩).lower ∧ (cell12622 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12622 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12622 ⟨47,by decide⟩).lower ∧ (cell12622 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12622 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12622 ⟨48,by decide⟩).lower ∧ (cell12622 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12622 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12622 ⟨49,by decide⟩).lower ∧ (cell12622 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12622 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12622 ⟨50,by decide⟩).lower ∧ (cell12622 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12622 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12622 ⟨51,by decide⟩).lower ∧ (cell12622 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12622 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12622 ⟨52,by decide⟩).lower ∧ (cell12622 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12622 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12622 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12622 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12622,cell12622,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12622 i).lower ∧
    (cell12622 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12622 i).upper ≤ (0.532 : ℝ) ∧
    (cell12622 i).centre ≤ (0.1 : ℝ) ∧ (cell12622 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12622 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12622 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12622

/-! The local source numeric instances at 12622 have no network premises. -/
namespace BstLean.Part269.N12622
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12622)
open BstLean.Part268 (cell12622)

noncomputable def sourceNumerics12622 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12622 (cell12622 i)
      scalarRow12622.M scalarRow12622.H scalarRow12622.xi := by
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
    energy_allowance := scalarRow12622.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12622]
    centre_nonneg := (scalarRow12622.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12622])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12622
/-! Actual 12623 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12623
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12623 ≤ (1.035919234742 : ℝ) := by
  have hr : (112.352125035532 : ℝ) ≤ √(12623 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.352125035532 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12623 12623 (11 / 1000) ≤
    (0.008507957026 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12623) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.352125035532 : ℝ) ≤ √(12623 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12623)
  have hdiv : K / √(12623 : ℝ) ≤ K / 112.352125035532 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.352125035532 ≤ (0.008507957026 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12623.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12623 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12623 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12623 := gPlus_lower 12623
end BstLean.Part269.N12623

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12623
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035919234741 : ℝ) ≤ wn 12623 := by
  have hn : √(12623 : ℝ) ≤ 112.352125035533 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12623 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.352125035533 ≤ 2 / √(12623 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253444252 : ℝ) ≤ rhoBar 12623 BstLean.Part154.csC ∧
    rhoBar 12623 BstLean.Part154.csC ≤ 0.000253444644 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035919234741 : ℝ) / (1.295212 * 12623) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035919234742 : ℝ) / (1.29521 * 12623) := by gcongr
      _ ≤ (0.000253444644 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12623 BstLean.Part154.csC) ≤ 0.001013842811 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12623 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12623 BstLean.Part154.csC) (piBar (rhoBar 12623 BstLean.Part154.csC)) ≤ 0.000193582785 ∧
    cc1 (rhoBar 12623 BstLean.Part154.csC) (piBar (rhoBar 12623 BstLean.Part154.csC)) ≤ 0.000123178000 ∧
    cc2 (rhoBar 12623 BstLean.Part154.csC) ≤ 0.000071505759 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12623 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12623 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12623 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12623 BstLean.Part154.csC * nuR (rhoBar 12623 BstLean.Part154.csC)) ≤ 0.000506905347 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253444644 : ℝ) * 0.001013842811 := by gcongr
      _ ≤ (0.000506905347 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12623 BstLean.Part154.csC) * nuR (rhoBar 12623 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001013842811 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12623 BstLean.Part154.csC) * rhoBar 12623 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253444644 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253444644 / 2 + 0.399 * 0.001013842811 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193582785 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506905347 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123178000 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253444644 / 1.414213562 := by gcongr
      _ ≤ (0.000071505759 : ℝ) := by norm_num

end BstLean.Part269.N12623

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12623
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12623 BstLean.Part154.csC) (piBar (rhoBar 12623 BstLean.Part154.csC)) ≤ 1.61834E-7 := by
  have hr0 : 0 ≤ rhoBar 12623 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12623 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12623 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12623 BstLean.Part154.csC) (piBar (rhoBar 12623 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12623 BstLean.Part154.csC) (piBar (rhoBar 12623 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12623 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193582785 : ℝ) ^ 2 + 0.000123178000 ^ 2 + 3 * 0.000071505759 ^ 2 +
        2 * 0.797885 * 0.000193582785 * 0.000123178000 + 2 * 0.000193582785 * 0.000071505759 +
        4 * 0.797885 * 0.000123178000 * 0.000071505759 := by gcongr
    _ ≤ (1.61834E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12623 BstLean.Part154.csC Θ ≤ 0.002645898688 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12623 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12623 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12623 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12623 BstLean.Part154.csC) (piBar (rhoBar 12623 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12623 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035919234742 * 1.61834E-7 / (0.000253444252 : ℝ) := by gcongr
    _ ≤ 0.002645898688 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12623 BstLean.Part154.csC Θ ≤ 0.002936070172 + 0.000668573594 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12623 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12623 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12623 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035919234742 : ℝ) * ((2 * Θ * 0.000253444644 +
        (6863 / 10000) * 0.000253444644 * 12623 * 0.001013842811) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002936070172 + 0.000668573594 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12623 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12623 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12623 0.011 Θ ∧ gammaRatio 12623 0.011 Θ ≤ 0.000087127715 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12623 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035919234742 : ℝ) * 0.525 / ((1 - 0.011) * 12623) := by gcongr
      _ ≤ (0.000087127715 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12623 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12623 0.011 Θ) :=
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
    badAllowance 12623 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12623 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12623 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12623 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12623 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12623 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12623 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12623 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12623 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12623 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12623 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035919234742 : ℝ) * 12623 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12623 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003612355568 + 0.003314472282 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12623

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12623
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12623 BstLean.Part154.csC) (piBar (rhoBar 12623 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12623 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12623 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12623 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12623 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12623 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12623 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12623 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12623 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12623 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12623 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12623 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12623 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12623 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12623 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052645884376 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12623) ≤ 0.010629416940 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12623 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035919234742)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010629416940 + 2 * 0.737676 / 12623) := by gcongr
    _ ≤ (0.052645884376 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12623 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12623

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12623
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500064881 : ℝ) ≤ plow 12623 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12623) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052859053517)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389096812) : eMP 12623 0.011 xi bn ≤ 0.001195776281 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12623 : ℝ) * (1 - 0.011))) ≤ 0.000591237240 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001389096812 / (12623 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591237240 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591237240 : ℝ) + 3.141593 * 0.052859053517 / (12623 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001195776281 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052859053517)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389096812) : PiBarMP 12623 12 0.011 xi bn ≤ 0.161747188831 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12623 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037270589102 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.732479610899 : ℝ) ≤ √((12623 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.352125035532 : ℝ) ≤ √(12623 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12623) ≤ 0.124006628788 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037270589102 + 0.052859053517 * 1.772454 / (2 * (111.732479610899 : ℝ))) * (1 + 0.001195776281) +
        8 / (12623 * 112.352125035532) + 0.124006628788 := by gcongr
    _ ≤ (0.161747188831 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052859053517)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389096812) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282556853051) :
    parallelOracle 12623 0.011 xi bn cd ≤ 0.162743968464 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12623 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12623 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500064881 : ℝ) ≤ plow 12623 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.352125035532 : ℝ) ≤ √(12623 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282556853051 : ℝ) / (2 * 0.560500064881 * 112.352125035532)) * 0.161747188831 +
        0.282556853051 ^ 2 / (2 * 0.560500064881 * 112.352125035532) := by gcongr
    _ ≤ (0.162743968464 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052859053517) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001389096812)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282556853051) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12623 12623 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500064881 : ℝ) ≤ plow 12623 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.352125035532 : ℝ) ≤ √(12623 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12623 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12623 Θ 1.22 ≤ 0.011803074482 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.352125035532 := by gcongr <;> linarith
      _ ≤ (0.011803074482 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12623 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12623 12623 0.011 ≤ 0.008507957026 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12623 12623 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12623 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12623 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12623 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12623 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162743968464 + 0.011803074482 + (0.008507957026 : ℝ) *
        (1 + 2 * (0.282556853051 + 0.011803074482) / (0.560500064881 * 112.352125035532))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12623]

end BstLean.Part269.N12623

/-! The original eight local profiles supply actual 12623 moment certificates. -/
namespace BstLean.Part269.N12623
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12623 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12623 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12623 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052859053517 ∧
    0 ≤ bN 12623 BstLean.Part154.csC (groupTheta g) ∧ bN 12623 BstLean.Part154.csC (groupTheta g) ≤ 0.001389096812 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12623 12623 0.011
      (momentAllowance 12623 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12623 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12623 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12623 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12623 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12623 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229910968675 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12623 0.011
      (momentAllowance 12623 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12623 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12623
/-! The actual computed-centre upper energy formula at 12623. -/
namespace BstLean.Part269.N12623
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12623

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12623
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12623)
open BstLean.Part268 (cell12623)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085718109902
  | 2 => 0.086665121113
  | 3 => 0.087610905843
  | 4 => 0.088557027290
  | 5 => 0.089505371283
  | 6 => 0.090458193553
  | 7 => 0.091418171338
  | 8 => 0.092388459334
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12623 12623 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12623 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003617997022 + 0.003320722551 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S10.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12623

/-! Actual upper energy certificates on all 43 source endpoints at 12623. -/
namespace BstLean.Part269.N12623
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12623)
open BstLean.Part268 (cell12623)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12623 (gMinus 12623) (1 - (cell12623 i).lower) ≤ 1 ∧
    energyUpper 12623 (gMinus 12623) (BstLean.Part211.gPlus 12623)
      (finiteEnergy 12623 12623 0.011) (1 - (cell12623 i).lower) ≤
      (cell12623 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨10,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨11,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨12,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨13,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨14,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨15,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨16,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨17,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨18,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨19,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨20,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨21,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨22,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨23,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨24,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨25,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨26,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨27,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨28,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨29,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨30,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨31,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨32,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨33,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨34,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨35,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨36,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨37,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨38,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨39,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨40,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨41,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨42,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨43,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨44,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨45,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨46,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨47,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨48,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨49,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨50,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨51,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12623) (by norm_num)
        (q := 1 - (cell12623 ⟨52,by decide⟩).lower)
        (by norm_num [cell12623]) (by norm_num [cell12623])
      exact ⟨E.1,E.2.trans (by norm_num [cell12623])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12623

/-! Source-cell containment and simple scalar guards at 12623. -/
namespace BstLean.Part269.N12623
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12623)
open BstLean.Part268 (cell12623)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12623 ⟨10,by decide⟩).lower ∧ (cell12623 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12623 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12623 ⟨11,by decide⟩).lower ∧ (cell12623 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12623 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12623 ⟨12,by decide⟩).lower ∧ (cell12623 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12623 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12623 ⟨13,by decide⟩).lower ∧ (cell12623 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12623 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12623 ⟨14,by decide⟩).lower ∧ (cell12623 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12623 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12623 ⟨15,by decide⟩).lower ∧ (cell12623 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12623 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12623 ⟨16,by decide⟩).lower ∧ (cell12623 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12623 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12623 ⟨17,by decide⟩).lower ∧ (cell12623 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12623 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12623 ⟨18,by decide⟩).lower ∧ (cell12623 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12623 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12623 ⟨19,by decide⟩).lower ∧ (cell12623 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12623 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12623 ⟨20,by decide⟩).lower ∧ (cell12623 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12623 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12623 ⟨21,by decide⟩).lower ∧ (cell12623 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12623 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12623 ⟨22,by decide⟩).lower ∧ (cell12623 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12623 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12623 ⟨23,by decide⟩).lower ∧ (cell12623 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12623 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12623 ⟨24,by decide⟩).lower ∧ (cell12623 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12623 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12623 ⟨25,by decide⟩).lower ∧ (cell12623 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12623 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12623 ⟨26,by decide⟩).lower ∧ (cell12623 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12623 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12623 ⟨27,by decide⟩).lower ∧ (cell12623 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12623 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12623 ⟨28,by decide⟩).lower ∧ (cell12623 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12623 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12623 ⟨29,by decide⟩).lower ∧ (cell12623 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12623 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12623 ⟨30,by decide⟩).lower ∧ (cell12623 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12623 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12623 ⟨31,by decide⟩).lower ∧ (cell12623 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12623 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12623 ⟨32,by decide⟩).lower ∧ (cell12623 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12623 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12623 ⟨33,by decide⟩).lower ∧ (cell12623 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12623 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12623 ⟨34,by decide⟩).lower ∧ (cell12623 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12623 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12623 ⟨35,by decide⟩).lower ∧ (cell12623 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12623 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12623 ⟨36,by decide⟩).lower ∧ (cell12623 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12623 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12623 ⟨37,by decide⟩).lower ∧ (cell12623 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12623 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12623 ⟨38,by decide⟩).lower ∧ (cell12623 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12623 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12623 ⟨39,by decide⟩).lower ∧ (cell12623 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12623 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12623 ⟨40,by decide⟩).lower ∧ (cell12623 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12623 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12623 ⟨41,by decide⟩).lower ∧ (cell12623 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12623 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12623 ⟨42,by decide⟩).lower ∧ (cell12623 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12623 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12623 ⟨43,by decide⟩).lower ∧ (cell12623 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12623 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12623 ⟨44,by decide⟩).lower ∧ (cell12623 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12623 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12623 ⟨45,by decide⟩).lower ∧ (cell12623 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12623 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12623 ⟨46,by decide⟩).lower ∧ (cell12623 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12623 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12623 ⟨47,by decide⟩).lower ∧ (cell12623 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12623 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12623 ⟨48,by decide⟩).lower ∧ (cell12623 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12623 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12623 ⟨49,by decide⟩).lower ∧ (cell12623 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12623 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12623 ⟨50,by decide⟩).lower ∧ (cell12623 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12623 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12623 ⟨51,by decide⟩).lower ∧ (cell12623 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12623 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12623 ⟨52,by decide⟩).lower ∧ (cell12623 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12623 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12623 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12623 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12623,cell12623,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12623 i).lower ∧
    (cell12623 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12623 i).upper ≤ (0.532 : ℝ) ∧
    (cell12623 i).centre ≤ (0.1 : ℝ) ∧ (cell12623 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12623 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12623 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12623

/-! The local source numeric instances at 12623 have no network premises. -/
namespace BstLean.Part269.N12623
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12623)
open BstLean.Part268 (cell12623)

noncomputable def sourceNumerics12623 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12623 (cell12623 i)
      scalarRow12623.M scalarRow12623.H scalarRow12623.xi := by
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
    energy_allowance := scalarRow12623.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12623]
    centre_nonneg := (scalarRow12623.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12623])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12623
/-! Actual 12624 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12624
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12624 ≤ (1.035917799507 : ℝ) := by
  have hr : (112.356575241505 : ℝ) ≤ √(12624 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.356575241505 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12624 12624 (11 / 1000) ≤
    (0.008507620041 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12624) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.356575241505 : ℝ) ≤ √(12624 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12624)
  have hdiv : K / √(12624 : ℝ) ≤ K / 112.356575241505 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.356575241505 ≤ (0.008507620041 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12624.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12624 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12624 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12624 := gPlus_lower 12624
end BstLean.Part269.N12624

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12624
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035917799506 : ℝ) ≤ wn 12624 := by
  have hn : √(12624 : ℝ) ≤ 112.356575241506 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12624 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.356575241506 ≤ 2 / √(12624 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253423824 : ℝ) ≤ rhoBar 12624 BstLean.Part154.csC ∧
    rhoBar 12624 BstLean.Part154.csC ≤ 0.000253424217 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035917799506 : ℝ) / (1.295212 * 12624) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035917799507 : ℝ) / (1.29521 * 12624) := by gcongr
      _ ≤ (0.000253424217 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12624 BstLean.Part154.csC) ≤ 0.001013761092 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12624 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12624 BstLean.Part154.csC) (piBar (rhoBar 12624 BstLean.Part154.csC)) ≤ 0.000193567182 ∧
    cc1 (rhoBar 12624 BstLean.Part154.csC) (piBar (rhoBar 12624 BstLean.Part154.csC)) ≤ 0.000123168072 ∧
    cc2 (rhoBar 12624 BstLean.Part154.csC) ≤ 0.000071499995 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12624 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12624 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12624 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12624 BstLean.Part154.csC * nuR (rhoBar 12624 BstLean.Part154.csC)) ≤ 0.000506864490 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253424217 : ℝ) * 0.001013761092 := by gcongr
      _ ≤ (0.000506864490 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12624 BstLean.Part154.csC) * nuR (rhoBar 12624 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001013761092 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12624 BstLean.Part154.csC) * rhoBar 12624 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253424217 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253424217 / 2 + 0.399 * 0.001013761092 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193567182 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506864490 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123168072 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253424217 / 1.414213562 := by gcongr
      _ ≤ (0.000071499995 : ℝ) := by norm_num

end BstLean.Part269.N12624

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12624
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12624 BstLean.Part154.csC) (piBar (rhoBar 12624 BstLean.Part154.csC)) ≤ 1.61808E-7 := by
  have hr0 : 0 ≤ rhoBar 12624 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12624 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12624 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12624 BstLean.Part154.csC) (piBar (rhoBar 12624 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12624 BstLean.Part154.csC) (piBar (rhoBar 12624 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12624 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193567182 : ℝ) ^ 2 + 0.000123168072 ^ 2 + 3 * 0.000071499995 ^ 2 +
        2 * 0.797885 * 0.000193567182 * 0.000123168072 + 2 * 0.000193567182 * 0.000071499995 +
        4 * 0.797885 * 0.000123168072 * 0.000071499995 := by gcongr
    _ ≤ (1.61808E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12624 BstLean.Part154.csC Θ ≤ 0.002645683183 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12624 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12624 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12624 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12624 BstLean.Part154.csC) (piBar (rhoBar 12624 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12624 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035917799507 * 1.61808E-7 / (0.000253423824 : ℝ) := by gcongr
    _ ≤ 0.002645683183 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12624 BstLean.Part154.csC Θ ≤ 0.002935825386 + 0.000668518783 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12624 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12624 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12624 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035917799507 : ℝ) * ((2 * Θ * 0.000253424217 +
        (6863 / 10000) * 0.000253424217 * 12624 * 0.001013761092) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002935825386 + 0.000668518783 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12624 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12624 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12624 0.011 Θ ∧ gammaRatio 12624 0.011 Θ ≤ 0.000087120693 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12624 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035917799507 : ℝ) * 0.525 / ((1 - 0.011) * 12624) := by gcongr
      _ ≤ (0.000087120693 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12624 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12624 0.011 Θ) :=
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
    badAllowance 12624 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676285396 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12624 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12624 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12624 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12624 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12624 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12624 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12624 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12624 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12624 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12624 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035917799507 : ℝ) * 12624 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676285396 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12624 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003612110782 + 0.003314201966 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12624

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12624
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12624 BstLean.Part154.csC) (piBar (rhoBar 12624 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12624 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12624 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12624 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12624 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12624 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12624 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12624 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12624 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12624 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12624 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12624 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12624 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12624 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12624 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052643776505 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12624) ≤ 0.010628995931 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12624 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035917799507)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010628995931 + 2 * 0.737676 / 12624) := by gcongr
    _ ≤ (0.052643776505 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12624 12 ≤ 0.0015 := by
  exact BstLean.Part269.S10.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12624

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12624
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500110654 : ℝ) ≤ plow 12624 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12624) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052858666815)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388983672) : eMP 12624 0.011 xi bn ≤ 0.001195680140 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12624 : ℝ) * (1 - 0.011))) ≤ 0.000591189745 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001388983672 / (12624 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591189745 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591189745 : ℝ) + 3.141593 * 0.052858666815 / (12624 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001195680140 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052858666815)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388983672) : PiBarMP 12624 12 0.011 xi bn ≤ 0.161740733537 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12624 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037269071253 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.736905273056 : ℝ) ≤ √((12624 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.356575241505 : ℝ) ≤ √(12624 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12624) ≤ 0.124001717148 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037269071253 + 0.052858666815 * 1.772454 / (2 * (111.736905273056 : ℝ))) * (1 + 0.001195680140) +
        8 / (12624 * 112.356575241505) + 0.124001717148 := by gcongr
    _ ≤ (0.161740733537 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052858666815)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388983672) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282553904197) :
    parallelOracle 12624 0.011 xi bn cd ≤ 0.162737442109 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12624 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12624 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500110654 : ℝ) ≤ plow 12624 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.356575241505 : ℝ) ≤ √(12624 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282553904197 : ℝ) / (2 * 0.560500110654 * 112.356575241505)) * 0.161740733537 +
        0.282553904197 ^ 2 / (2 * 0.560500110654 * 112.356575241505) := by gcongr
    _ ≤ (0.162737442109 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052858666815) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388983672)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282553904197) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12624 12624 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500110654 : ℝ) ≤ plow 12624 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.356575241505 : ℝ) ≤ √(12624 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12624 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12624 Θ 1.22 ≤ 0.011802606988 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.356575241505 := by gcongr <;> linarith
      _ ≤ (0.011802606988 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12624 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12624 12624 0.011 ≤ 0.008507620041 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12624 12624 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12624 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12624 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12624 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12624 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162737442109 + 0.011802606988 + (0.008507620041 : ℝ) *
        (1 + 2 * (0.282553904197 + 0.011802606988) / (0.560500110654 * 112.356575241505))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12624]

end BstLean.Part269.N12624

/-! The original eight local profiles supply actual 12624 moment certificates. -/
namespace BstLean.Part269.N12624
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12624 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12624 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12624 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052858666815 ∧
    0 ≤ bN 12624 BstLean.Part154.csC (groupTheta g) ∧ bN 12624 BstLean.Part154.csC (groupTheta g) ≤ 0.001388983672 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12624 12624 0.011
      (momentAllowance 12624 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12624 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12624 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12624 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12624 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12624 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229910127692 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12624 0.011
      (momentAllowance 12624 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12624 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12624
/-! The actual computed-centre upper energy formula at 12624. -/
namespace BstLean.Part269.N12624
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12624

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12624
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12624)
open BstLean.Part268 (cell12624)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085715107364
  | 2 => 0.086662061419
  | 3 => 0.087607780335
  | 4 => 0.088553825341
  | 5 => 0.089502079952
  | 6 => 0.090454797199
  | 7 => 0.091414651188
  | 8 => 0.092384793010
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12624 12624 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12624 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003617997022 + 0.003320722551 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S10.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S10.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12624

/-! Actual upper energy certificates on all 43 source endpoints at 12624. -/
namespace BstLean.Part269.N12624
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12624)
open BstLean.Part268 (cell12624)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12624 (gMinus 12624) (1 - (cell12624 i).lower) ≤ 1 ∧
    energyUpper 12624 (gMinus 12624) (BstLean.Part211.gPlus 12624)
      (finiteEnergy 12624 12624 0.011) (1 - (cell12624 i).lower) ≤
      (cell12624 i).energy := by
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
      have E := BstLean.Part269.S10.uniformEnergy10 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨10,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy11 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨11,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy12 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨12,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy13 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨13,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy14 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨14,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy15 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨15,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy16 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨16,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy17 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨17,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy18 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨18,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy19 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨19,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy20 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨20,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy21 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨21,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy22 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨22,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy23 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨23,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy24 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨24,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy25 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨25,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy26 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨26,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy27 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨27,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy28 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨28,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy29 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨29,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy30 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨30,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy31 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨31,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy32 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨32,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy33 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨33,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy34 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨34,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy35 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨35,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy36 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨36,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy37 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨37,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy38 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨38,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy39 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨39,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy40 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨40,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy41 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨41,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy42 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨42,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy43 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨43,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy44 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨44,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy45 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨45,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy46 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨46,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy47 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨47,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy48 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨48,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy49 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨49,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy50 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨50,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy51 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨51,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S10.uniformEnergy52 (n := 12624) (by norm_num)
        (q := 1 - (cell12624 ⟨52,by decide⟩).lower)
        (by norm_num [cell12624]) (by norm_num [cell12624])
      exact ⟨E.1,E.2.trans (by norm_num [cell12624])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12624

/-! Source-cell containment and simple scalar guards at 12624. -/
namespace BstLean.Part269.N12624
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12624)
open BstLean.Part268 (cell12624)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12624 ⟨10,by decide⟩).lower ∧ (cell12624 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12624 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12624 ⟨11,by decide⟩).lower ∧ (cell12624 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12624 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12624 ⟨12,by decide⟩).lower ∧ (cell12624 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12624 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12624 ⟨13,by decide⟩).lower ∧ (cell12624 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12624 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12624 ⟨14,by decide⟩).lower ∧ (cell12624 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12624 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12624 ⟨15,by decide⟩).lower ∧ (cell12624 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12624 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12624 ⟨16,by decide⟩).lower ∧ (cell12624 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12624 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12624 ⟨17,by decide⟩).lower ∧ (cell12624 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12624 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12624 ⟨18,by decide⟩).lower ∧ (cell12624 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12624 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12624 ⟨19,by decide⟩).lower ∧ (cell12624 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12624 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12624 ⟨20,by decide⟩).lower ∧ (cell12624 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12624 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12624 ⟨21,by decide⟩).lower ∧ (cell12624 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12624 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12624 ⟨22,by decide⟩).lower ∧ (cell12624 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12624 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12624 ⟨23,by decide⟩).lower ∧ (cell12624 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12624 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12624 ⟨24,by decide⟩).lower ∧ (cell12624 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12624 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12624 ⟨25,by decide⟩).lower ∧ (cell12624 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12624 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12624 ⟨26,by decide⟩).lower ∧ (cell12624 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12624 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12624 ⟨27,by decide⟩).lower ∧ (cell12624 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12624 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12624 ⟨28,by decide⟩).lower ∧ (cell12624 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12624 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12624 ⟨29,by decide⟩).lower ∧ (cell12624 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12624 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12624 ⟨30,by decide⟩).lower ∧ (cell12624 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12624 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12624 ⟨31,by decide⟩).lower ∧ (cell12624 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12624 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12624 ⟨32,by decide⟩).lower ∧ (cell12624 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12624 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12624 ⟨33,by decide⟩).lower ∧ (cell12624 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12624 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12624 ⟨34,by decide⟩).lower ∧ (cell12624 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12624 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12624 ⟨35,by decide⟩).lower ∧ (cell12624 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12624 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12624 ⟨36,by decide⟩).lower ∧ (cell12624 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12624 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12624 ⟨37,by decide⟩).lower ∧ (cell12624 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12624 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12624 ⟨38,by decide⟩).lower ∧ (cell12624 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12624 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12624 ⟨39,by decide⟩).lower ∧ (cell12624 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12624 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12624 ⟨40,by decide⟩).lower ∧ (cell12624 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12624 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12624 ⟨41,by decide⟩).lower ∧ (cell12624 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12624 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12624 ⟨42,by decide⟩).lower ∧ (cell12624 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12624 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12624 ⟨43,by decide⟩).lower ∧ (cell12624 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12624 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12624 ⟨44,by decide⟩).lower ∧ (cell12624 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12624 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12624 ⟨45,by decide⟩).lower ∧ (cell12624 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12624 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12624 ⟨46,by decide⟩).lower ∧ (cell12624 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12624 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12624 ⟨47,by decide⟩).lower ∧ (cell12624 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12624 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12624 ⟨48,by decide⟩).lower ∧ (cell12624 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12624 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12624 ⟨49,by decide⟩).lower ∧ (cell12624 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12624 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12624 ⟨50,by decide⟩).lower ∧ (cell12624 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12624 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12624 ⟨51,by decide⟩).lower ∧ (cell12624 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12624 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12624 ⟨52,by decide⟩).lower ∧ (cell12624 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12624 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12624 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12624 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12624,cell12624,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12624 i).lower ∧
    (cell12624 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12624 i).upper ≤ (0.532 : ℝ) ∧
    (cell12624 i).centre ≤ (0.1 : ℝ) ∧ (cell12624 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12624 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12624 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12624

/-! The local source numeric instances at 12624 have no network premises. -/
namespace BstLean.Part269.N12624
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12624)
open BstLean.Part268 (cell12624)

noncomputable def sourceNumerics12624 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12624 (cell12624 i)
      scalarRow12624.M scalarRow12624.H scalarRow12624.xi := by
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
    energy_allowance := scalarRow12624.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12624]
    centre_nonneg := (scalarRow12624.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D10.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12624])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12624